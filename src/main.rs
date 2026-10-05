use std::{
    error::Error,
    path::{Path, PathBuf},
    collections::HashMap,
    hash::{DefaultHasher, Hash, Hasher},
    process::Command,
    sync::{
        Arc, OnceLock,
        mpsc::{self, Receiver},
    },
    time::{Duration, Instant},
};

use ratatui::{
    DefaultTerminal, Frame,
    crossterm::event::{self, Event, KeyCode, KeyEvent, KeyEventKind, KeyModifiers},
    layout::{Position, Rect},
    style::{Color, Modifier, Style},
    text::{Line, Span},
    widgets::{Block, Clear, Paragraph, Wrap},
};
use similar::{DiffOp, TextDiff};
use syntect::{
    easy::HighlightLines,
    highlighting::{self, FontStyle, Theme},
    parsing::SyntaxSet,
    util::LinesWithEndings,
};
use two_face::theme::EmbeddedThemeName;
use unicode_width::UnicodeWidthChar;

const DEL_BG: Color = Color::Rgb(70, 25, 25);
const ADD_BG: Color = Color::Rgb(25, 60, 25);
/// Conflict being decided, and conflicts not reached yet.
const CUR_BG: Color = Color::Rgb(85, 65, 15);
const PENDING_BG: Color = Color::Rgb(50, 50, 50);
/// Unchanged lines kept around each change when eliding.
const CONTEXT: usize = 3;

fn git_cmd(root: &Path, args: &[&str]) -> Command {
    let mut cmd = Command::new("git");
    cmd.current_dir(root)
        // Never write the index behind a running pull/push; never prompt on the TUI's terminal.
        .env("GIT_OPTIONAL_LOCKS", "0")
        .env("GIT_TERMINAL_PROMPT", "0")
        .args(args);
    cmd
}

fn git_bytes(root: &Path, args: &[&str]) -> Result<Vec<u8>, String> {
    run_git(git_cmd(root, args))
}

fn run_git(mut cmd: Command) -> Result<Vec<u8>, String> {
    let out = cmd.output().map_err(|e| e.to_string())?;
    if out.status.success() {
        Ok(out.stdout)
    } else {
        Err(String::from_utf8_lossy(&out.stderr).trim().to_string())
    }
}

fn git(root: &Path, args: &[&str]) -> Result<String, String> {
    git_bytes(root, args).map(|b| String::from_utf8_lossy(&b).trim_end().to_string())
}

/// Fetches all remotes for the background refresh. Nobody asked for it, so ssh
/// must not stop to ask for a passphrase or a host key. True if any remote ref moved.
fn background_fetch(root: &Path) -> bool {
    if git(root, &["remote"]).unwrap_or_default().is_empty() {
        return false;
    }
    let refs = || git(root, &["for-each-ref", "--format=%(refname) %(objectname)", "refs/remotes"]).ok();
    let before = refs();
    let ssh = std::env::var("GIT_SSH_COMMAND")
        .ok()
        .or_else(|| git(root, &["config", "core.sshCommand"]).ok())
        .unwrap_or_else(|| "ssh".into());
    let mut cmd = git_cmd(root, &["fetch", "--all", "--prune", "--quiet"]);
    cmd.env("GIT_SSH_COMMAND", format!("{ssh} -o BatchMode=yes"));
    run_git(cmd).is_ok() && refs() != before
}

#[derive(Clone)]
struct Entry {
    path: String,
    orig: Option<String>,
    x: u8,
    y: u8,
    /// Lines added and removed; None for binary files.
    stat: Option<(usize, usize)>,
}

impl Entry {
    fn staged(&self) -> bool {
        !matches!(self.x, b' ' | b'?')
    }
    fn unstaged(&self) -> bool {
        self.y != b' '
    }
    fn is_new(&self) -> bool {
        matches!(self.x, b'A' | b'?')
    }
    fn is_deleted(&self) -> bool {
        self.x == b'D' || self.y == b'D'
    }
    fn is_conflict(&self) -> bool {
        matches!((self.x, self.y), (b'U', _) | (_, b'U') | (b'A', b'A') | (b'D', b'D'))
    }
    fn dirs(&self) -> Vec<&str> {
        self.path.rsplit_once('/').map_or(vec![], |(d, _)| d.split('/').collect())
    }
    fn name(&self) -> &str {
        self.path.rsplit('/').next().unwrap_or(&self.path)
    }
}

#[derive(Default, Clone)]
struct Diff {
    /// (old line, new line, changed)
    rows: Vec<(Option<usize>, Option<usize>, bool)>,
    old: Vec<Line<'static>>,
    new: Vec<Line<'static>>,
    /// Conflict row ranges (start, len) while resolving.
    conflicts: Vec<(usize, usize)>,
    /// `lines_cache` keys of `old` and `new`; their highlighting replaces the plain lines when it arrives.
    keys: (u64, u64),
}

/// Part of a file with conflict markers.
enum Seg {
    Common(Vec<String>),
    /// Left (ours) and right (theirs) lines.
    Conflict(Vec<String>, Vec<String>),
}

/// Splits text with conflict markers into segments, plus the labels after `<<<<<<<` and
/// `>>>>>>>`. The diff3 base section is dropped. None when there are no complete conflicts.
fn parse_conflicts(text: &str) -> Option<(Vec<Seg>, String, String)> {
    let (mut segs, mut left, mut right) = (vec![], String::new(), String::new());
    let (mut common, mut ours, mut theirs) = (vec![], vec![], vec![]);
    // 0 common, 1 ours, 2 base, 3 theirs
    let mut part = 0;
    for line in text.split_inclusive('\n') {
        let is = |m: &str| line.starts_with(m) && line[7..].chars().next().is_none_or(char::is_whitespace);
        if part == 0 && is("<<<<<<<") {
            left = line[7..].trim().to_string();
            segs.push(Seg::Common(std::mem::take(&mut common)));
            part = 1;
        } else if part == 1 && is("|||||||") {
            part = 2;
        } else if (part == 1 || part == 2) && is("=======") {
            part = 3;
        } else if part == 3 && is(">>>>>>>") {
            right = line[7..].trim().to_string();
            segs.push(Seg::Conflict(std::mem::take(&mut ours), std::mem::take(&mut theirs)));
            part = 0;
        } else {
            match part {
                0 => common.push(line.to_string()),
                1 => ours.push(line.to_string()),
                3 => theirs.push(line.to_string()),
                _ => {}
            }
        }
    }
    if part != 0 || !segs.iter().any(|s| matches!(s, Seg::Conflict(..))) {
        return None;
    }
    segs.push(Seg::Common(common));
    Some((segs, left, right))
}

/// Conflict resolution in progress: files to go through and choices for the current one.
struct Resolve {
    files: Vec<String>,
    file: usize,
    /// Parsed markers; None for a whole-file conflict such as modify/delete.
    segs: Option<Vec<Seg>>,
    labels: (String, String),
    /// Per conflict: Some(true) keeps left, Some(false) keeps right.
    choices: Vec<Option<bool>>,
    cur: usize,
}

#[derive(Clone, PartialEq)]
enum Step {
    Pull,
    PullRebase,
    Push,
    /// Push over a diverged remote branch, unless it moved since we last saw it.
    ForcePush,
    /// Remote and branch to delete there.
    DeleteRemote(String, String),
    Stash,
    StashPop,
    /// Remote and ref to fetch.
    Fetch(String, String),
    Merge(String),
    CherryPick(String),
}

/// Result of a run of steps: message, the steps after a failed one, and which failed.
struct Outcome {
    res: Result<String, String>,
    rest: Vec<Step>,
    failed: Option<Step>,
    /// A merge, rebase or pick paused with nothing left to resolve (rerere with
    /// autoupdate resolved it); it only needs continuing.
    paused: bool,
    /// A push was refused because the remote branch has commits this one doesn't.
    rejected: bool,
}

/// The rebase, merge, cherry-pick or revert stopped part way, as its git command.
fn current_op(root: &Path) -> Option<&'static str> {
    // The git dir never moves while tit runs, so look it up once.
    static GIT_DIR: OnceLock<Option<PathBuf>> = OnceLock::new();
    let gd = GIT_DIR.get_or_init(|| git(root, &["rev-parse", "--absolute-git-dir"]).ok().map(PathBuf::from)).as_ref()?;
    [
        ("rebase-merge", "rebase"),
        ("rebase-apply", "rebase"),
        ("MERGE_HEAD", "merge"),
        ("CHERRY_PICK_HEAD", "cherry-pick"),
        ("REVERT_HEAD", "revert"),
    ]
    .into_iter()
    .find(|(f, _)| gd.join(f).exists())
    .map(|(_, op)| op)
}

fn in_progress(root: &Path) -> bool {
    current_op(root).is_some()
}

fn has_conflicts(root: &Path) -> bool {
    !git(root, &["diff", "--name-only", "--diff-filter=U"]).unwrap_or_default().is_empty()
}

/// Runs git network steps in order; meant for a background thread.
/// A failure that leaves conflicts keeps the remaining steps for after resolution.
/// Any other failure pops a stash this run made, so local changes come back.
fn run_steps(root: &Path, steps: &[Step]) -> Outcome {
    // Only an operation these steps started counts as paused.
    let was_in_progress = in_progress(root);
    for (i, step) in steps.iter().enumerate() {
        let res = match step {
            Step::Pull => git(root, &["pull", "--no-edit"]),
            Step::PullRebase => git(root, &["pull", "--rebase"]),
            Step::Push if git(root, &["rev-parse", "--abbrev-ref", "@{u}"]).is_ok() => git(root, &["push"]),
            Step::Push => match git(root, &["remote"]).unwrap_or_default().lines().next() {
                Some(remote) => git(root, &["push", "-u", remote, "HEAD"]),
                None => Err("no remote to push to".into()),
            },
            // --force-if-includes: a background fetch must not make the lease pass.
            Step::ForcePush => git(root, &["push", "--force-with-lease", "--force-if-includes"]),
            Step::DeleteRemote(remote, name) => git(root, &["push", remote, "--delete", name]),
            Step::Stash => git(root, &["stash", "push", "-u", "-m", "tit sync"]),
            Step::StashPop => git(root, &["stash", "pop"]),
            Step::Fetch(remote, rref) => git(root, &["fetch", remote, rref]),
            Step::Merge(rev) => git(root, &["merge", "--no-edit", rev]),
            Step::CherryPick(sha) => {
                let mut args = vec!["cherry-pick"];
                if git(root, &["rev-parse", "-q", "--verify", &format!("{sha}^2")]).is_ok() {
                    args.extend(["-m", "1"]); // merge: pick relative to the first parent
                }
                git(root, &[&args[..], &[sha]].concat())
            }
        };
        if let Err(err) = res {
            let rest = steps[i + 1..].to_vec();
            let failed = Some(step.clone());
            let mut msg = git_err(&err);
            let rejected = *step == Step::Push && err.contains("[rejected]");
            if *step == Step::ForcePush && err.contains("[rejected]") {
                msg = "force push refused: the remote has new commits you haven't pulled".into();
            }
            if let Step::CherryPick(_) = step
                && err.contains("now empty")
            {
                _ = git(root, &["cherry-pick", "--abort"]); // leaves the sequencer running otherwise
                msg = "nothing to cherry-pick: those changes are already here".into();
            } else if has_conflicts(root) {
                return Outcome { res: Err(msg), rest, failed, paused: false, rejected };
            } else if !was_in_progress && in_progress(root) {
                return Outcome { res: Err(msg), rest, failed, paused: true, rejected };
            }
            if rest.contains(&Step::StashPop) && git(root, &["stash", "pop"]).is_err() {
                msg += " (local changes still stashed)";
            }
            return Outcome { res: Err(msg), rest: vec![], failed, paused: false, rejected };
        }
    }
    Outcome { res: Ok(String::new()), rest: vec![], failed: None, paused: false, rejected: false }
}

#[derive(Clone, Copy, PartialEq)]
enum Mode {
    /// Working tree changes; staging and committing.
    Status,
    /// Commit list for the current branch.
    History,
    /// Changes in the selected commit.
    Commit,
    /// Branch list: check out or create.
    Branches,
    /// Tracked files; pick one to see its history.
    Files,
    /// Going through merge conflicts one at a time.
    Resolve,
}

/// `shown` entry for the "create branch" row in the branch list.
const CREATE: usize = usize::MAX;

/// Action waiting for confirmation.
enum Action {
    /// Throw away all changes to a file, staged and unstaged.
    Discard(Entry),
    /// Add a commit that reverts the given sha.
    Revert(String),
    Merge(String),
    /// Fetch remote + ref, then merge the remote-tracking branch.
    FetchMerge(String, String, String),
    ForcePush,
    /// Pull, then push.
    Sync,
    /// Local branch, and whether to delete it even when unmerged.
    DeleteBranch(String, bool),
    /// Remote and branch name there.
    DeleteRemote(String, String),
    /// Leave conflict resolution; `r` picks it up again.
    Pause,
    /// Undo the stopped merge, rebase, pick or revert (or a conflicted stash pop).
    Abort,
    /// Carry on with a stopped operation that has nothing left to resolve.
    Continue,
}

/// Confirmation modal: `y` runs `yes`, `o` runs `alt` if given, `n` cancels.
struct Confirm {
    prompt: String,
    yes: (String, Action),
    alt: Option<(String, Action)>,
}

/// Picks the most useful line of git's stderr: the first `error:`/`fatal:` line, else the last.
fn git_err(err: &str) -> String {
    let line = err.lines().find(|l| l.starts_with("error:") || l.starts_with("fatal:"));
    line.or(err.lines().last()).unwrap_or("git failed").to_string()
}

/// Which history: revision and file, None for the current branch and all files.
type LogKey = (Option<String>, Option<String>);

#[derive(Clone)]
struct LogEntry {
    sha: String,
    /// First parent; None for a root commit.
    parent: Option<String>,
    short: String,
    subject: String,
    author: String,
    date: String,
}

/// Git's empty tree, to diff against when there is no HEAD.
const EMPTY_TREE: &str = "4b825dc642cb6eb9a060e54bf8d69288fbee4904";

/// Parses `--numstat -z` output into path -> (added, removed); None for binary files.
fn numstat(raw: &str) -> HashMap<String, Option<(usize, usize)>> {
    let mut out = HashMap::new();
    let mut fields = raw.split('\0');
    while let Some(rec) = fields.next() {
        let mut parts = rec.splitn(3, '\t');
        let (Some(a), Some(d), Some(p)) = (parts.next(), parts.next(), parts.next()) else { continue };
        // Renames leave the path empty and follow with old and new paths.
        let path = if p.is_empty() {
            fields.next();
            fields.next().unwrap_or("")
        } else {
            p
        };
        out.insert(path.to_string(), a.parse().ok().zip(d.parse().ok()));
    }
    out
}

/// Commits of `rev` (default: HEAD), optionally only those touching `file`.
fn read_log(root: &Path, rev: Option<&str>, file: Option<&str>) -> Vec<LogEntry> {
    let mut args = vec!["log", "-n", "1000", "--date=format:%y-%m-%d %H:%M", "--format=%H%x1f%P%x1f%h%x1f%s%x1f%an%x1f%ad"];
    args.extend(rev);
    if let Some(f) = file {
        args.extend(["--follow", "--", f]);
    }
    // chisle: last 1000 commits; page in more if anyone scrolls that far.
    git(root, &args)
        .unwrap_or_default()
        .lines()
        .filter_map(|l| {
            let p: Vec<&str> = l.split('\x1f').collect();
            let [sha, parents, short, subject, author, date] = p[..] else { return None };
            let s = |x: &str| x.to_string();
            let parent = parents.split(' ').next().filter(|p| !p.is_empty()).map(s);
            Some(LogEntry { sha: s(sha), parent, short: s(short), subject: s(subject), author: s(author), date: s(date) })
        })
        .collect()
}

/// Files changed by `sha` against its first parent, in one git call.
fn commit_entries(root: &Path, sha: &str, parent: Option<&str>) -> Vec<Entry> {
    let mut args = vec!["diff-tree", "-r", "-z", "-M", "--raw", "--numstat", "--no-commit-id"];
    args.extend(match parent {
        Some(p) => [p, sha],
        None => ["--root", sha],
    });
    let raw = git(root, &args).unwrap_or_default();
    // Raw records (":modes shas status", path[, new path]) come first, then numstat.
    let mut fields = raw.split('\0').peekable();
    let mut out = vec![];
    while let Some(rec) = fields.next_if(|f| f.starts_with(':')) {
        let x = rec.rsplit(' ').next().and_then(|st| st.bytes().next()).unwrap_or(b'M');
        let p = fields.next().unwrap_or("").to_string();
        let (orig, path) = match x {
            b'R' | b'C' => (Some(p), fields.next().unwrap_or("").to_string()),
            _ => (None, p),
        };
        out.push(Entry { path, orig, x, y: b' ', stat: None });
    }
    let stats = numstat(&fields.collect::<Vec<_>>().join("\0"));
    for e in &mut out {
        e.stat = stats.get(&e.path).copied().flatten();
    }
    sort_entries(&mut out);
    out
}

/// Parses `status --porcelain=v2 -z` entries.
fn status_entries(raw: &str) -> Vec<Entry> {
    let mut fields = raw.split('\0');
    let mut out = vec![];
    while let Some(f) = fields.next() {
        // Space-separated fields before the path, which may itself hold spaces.
        let n = match f.as_bytes().first() {
            Some(b'1') => 9,
            Some(b'2') => 10,
            Some(b'u') => 11,
            Some(b'?') => {
                out.push(Entry { path: f[2..].to_string(), orig: None, x: b'?', y: b'?', stat: None });
                continue;
            }
            _ => continue,
        };
        let parts: Vec<&str> = f.splitn(n, ' ').collect();
        let [_, xy, .., path] = parts[..] else { continue };
        let [x, y] = [xy.as_bytes()[0], xy.as_bytes()[1]].map(|c| if c == b'.' { b' ' } else { c });
        let orig = f.starts_with('2').then(|| fields.next().unwrap_or("").to_string());
        out.push(Entry { path: path.to_string(), orig, x, y, stat: None });
    }
    out
}

fn sort_entries(v: &mut [Entry]) {
    v.sort_by(|a, b| (a.dirs(), a.name()).cmp(&(b.dirs(), b.name())));
}

/// Prefixes `lines` with a header label column: `LABEL │ `, blank label after the first line.
/// At most `max` lines around line `at`, with a note in place of each hidden run.
fn crop(mut lines: Vec<Line<'static>>, at: usize, max: usize) -> Vec<Line<'static>> {
    if lines.len() <= max {
        return lines;
    }
    let start = at.saturating_sub(max / 2).min(lines.len() - max);
    let (above, below) = (start, lines.len() - start - max);
    lines.truncate(start + max);
    lines.drain(..start);
    let more = |n| Line::styled(format!("… {n} more"), Style::new().fg(Color::DarkGray));
    if above > 0 {
        lines[0] = more(above + 1);
    }
    if below > 0 {
        lines[max - 1] = more(below + 1);
    }
    lines
}

fn labeled(name: &str, lines: Vec<Line<'static>>) -> Vec<Line<'static>> {
    lines
        .into_iter()
        .enumerate()
        .map(|(n, l)| {
            let mut spans = vec![Span::raw(if n == 0 { format!("{name:<6}") } else { " ".repeat(6) }), Span::raw(" │ ")];
            spans.extend(l.spans);
            Line::from(spans)
        })
        .collect()
}

/// How diff blocks are laid out.
#[derive(Clone, Copy, PartialEq)]
enum Layout {
    /// Side by side for blocks with in-place changes, full width for pure inserts/deletes.
    Hybrid,
    Split,
    Unified,
}

/// Cycle order: layout, config value, name shown when switching.
const LAYOUTS: [(Layout, &str, &str); 3] =
    [(Layout::Hybrid, "hybrid", "hybrid"), (Layout::Split, "split", "side by side"), (Layout::Unified, "unified", "unified")];

/// One screen line of the diff: left, right, and their backgrounds.
/// No right side means the line spans the full width (unified).
type VisRow = (Line<'static>, Option<Line<'static>>, Option<Color>, Option<Color>);

/// Highlighted old and new text, each with its cache key.
type Highlighted = [(u64, Vec<Line<'static>>); 2];

struct App {
    root: PathBuf,
    root_name: String,
    branch: String,
    status: String,
    mode: Mode,
    /// Files shown in the header: working tree changes, or the viewed commit's files.
    entries: Vec<Entry>,
    cur: usize,
    log: Vec<LogEntry>,
    /// Selected commit, as an index into `log`.
    sel: usize,
    /// Modal search text, and the `log` or `branches` indices that match it.
    query: String,
    shown: Vec<usize>,
    /// Selected row in `shown`.
    pos: usize,
    list_scroll: usize,
    /// Rows in the modal's list at the last draw.
    list_page: usize,
    /// Branch names and whether each is a remote-tracking branch.
    branches: Vec<(String, bool)>,
    /// Tracked files, for the file list.
    files: Vec<String>,
    /// File the history modal is limited to.
    hist_file: Option<String>,
    /// Files changed by the selected log entry.
    log_files: Vec<Entry>,
    /// Logs by (rev, file), shown at once while a fresh one loads in `log_rx`.
    log_cache: HashMap<LogKey, Vec<LogEntry>>,
    log_rx: Option<Receiver<(LogKey, Vec<LogEntry>)>>,
    /// Files of each commit seen; one commit's load at a time runs in `files_rx`.
    files_cache: HashMap<String, Vec<Entry>>,
    files_rx: Option<Receiver<(String, Vec<Entry>)>>,
    /// Repo state the last refresh saw, from `signature`.
    sig: String,
    /// Working tree entries, file, diff and scroll to restore when leaving a commit.
    saved: Option<(Vec<Entry>, usize, Diff, usize)>,
    diff: Diff,
    /// Diff rows wrapped to the screen width in `vis_width`; rebuilt when it changes.
    vis: Vec<VisRow>,
    vis_width: usize,
    /// Diff row to scroll to on the next rewrap.
    jump: Option<usize>,
    /// Hide unchanged lines away from changes.
    elide: bool,
    layout: Layout,
    scroll: usize,
    page: usize,
    commit: Option<String>,
    resolve: Option<Resolve>,
    /// Running network steps.
    busy: Option<Receiver<Outcome>>,
    /// Steps to run once conflicts are resolved.
    pending: Vec<Step>,
    /// Conflicts came from popping a stash, which then needs dropping.
    stash_conflict: bool,
    /// Confirmation modal: prompt and the action to run on yes.
    confirm: Option<Confirm>,
    /// New branch name being typed, from the viewed commit.
    new_branch: Option<String>,
    /// Branch modal: typing goes to the search box (else letters are commands).
    search_focus: bool,
    /// Revision the history modal lists, when not the current branch.
    hist_rev: Option<String>,
    /// Commit popup is amending HEAD: its original subject, and whether HEAD is pushed.
    amend: Option<(String, bool)>,
    /// Background fetch running, and when the last one started.
    fetching: Option<Receiver<bool>>,
    last_fetch: Option<Instant>,
    /// Steps (and their labels) waiting for the fetch to finish.
    queued: Option<(Vec<Step>, String, String)>,
    /// Key list overlay.
    help: bool,
    msg: String,
    ss: Arc<SyntaxSet>,
    theme: Arc<Theme>,
    /// Highlighted lines by hash of (path, text), so files seen before show at once.
    lines_cache: HashMap<u64, Vec<Line<'static>>>,
    /// Highlighting off the UI thread, as (key, lines) for old and new.
    hl_rx: Option<Receiver<Highlighted>>,
}

impl App {
    fn new(root: PathBuf) -> Self {
        let root_name = root.file_name().map_or("/".into(), |n| n.to_string_lossy().into_owned());
        let mut app = App {
            root,
            root_name,
            branch: String::new(),
            status: String::new(),
            mode: Mode::Status,
            entries: vec![],
            cur: 0,
            log: vec![],
            sel: 0,
            query: String::new(),
            shown: vec![],
            pos: 0,
            list_scroll: 0,
            list_page: 1,
            branches: vec![],
            files: vec![],
            hist_file: None,
            log_files: vec![],
            log_cache: HashMap::new(),
            log_rx: None,
            files_cache: HashMap::new(),
            files_rx: None,
            saved: None,
            sig: String::new(),
            diff: Diff::default(),
            vis: vec![],
            vis_width: 0,
            jump: None,
            elide: true,
            layout: Layout::Hybrid,
            resolve: None,
            busy: None,
            pending: vec![],
            stash_conflict: false,
            scroll: 0,
            page: 1,
            commit: None,
            confirm: None,
            new_branch: None,
            search_focus: false,
            hist_rev: None,
            amend: None,
            fetching: None,
            last_fetch: None,
            queued: None,
            help: false,
            msg: String::new(),
            ss: Arc::new(two_face::syntax::extra_newlines()),
            theme: Arc::new(two_face::theme::extra().get(EmbeddedThemeName::Ansi).clone()),
            lines_cache: HashMap::new(),
            hl_rx: None,
        };
        // Saved in git's global config; on unless set to false.
        app.elide = app.git(&["config", "--get", "--type=bool", "tit.elide"]).map_or(true, |v| v != "false");
        let saved = app.git(&["config", "--get", "tit.layout"]).unwrap_or_default();
        app.layout = LAYOUTS.iter().find(|l| l.1 == saved).map_or(Layout::Hybrid, |l| l.0);
        app.refresh();
        // Load the branch's history now so the first h is instant.
        app.start_log_load();
        app
    }

    fn git(&self, args: &[&str]) -> Result<String, String> {
        git(&self.root, args)
    }

    fn refresh(&mut self) {
        let st = self.git(&["status", "--porcelain=v2", "--branch", "-z", "--untracked-files=all"]).unwrap_or_default();
        self.refresh_from(&st);
    }

    /// Reloads everything from `status --porcelain=v2 --branch -z --untracked-files=all` output.
    fn refresh_from(&mut self, st: &str) {
        let prev = self.entries.get(self.cur).map(|e| e.path.clone());
        let has_head = self.parse_head(st);
        self.load_entries(st, has_head);
        self.sig = signature_of(&self.root, st, &self.paths());
        // No partial staging: a staged file edited since gets its new version staged.
        let partial: Vec<String> = self
            .entries
            .iter()
            .filter(|e| e.staged() && e.unstaged() && !e.is_conflict())
            .map(|e| e.path.clone())
            .collect();
        if !partial.is_empty() {
            let args = [&["add", "-A", "--"][..], &partial.iter().map(String::as_str).collect::<Vec<_>>()].concat();
            if let Err(err) = self.git(&args) {
                self.msg = git_err(&err);
            }
            let st = self.git(&["status", "--porcelain=v2", "--branch", "-z", "--untracked-files=all"]).unwrap_or_default();
            self.load_entries(&st, has_head);
            self.sig = signature_of(&self.root, &st, &self.paths());
        }

        let same = prev.as_deref().and_then(|p| self.entries.iter().position(|e| e.path == p));
        self.cur = same.unwrap_or(self.cur.min(self.entries.len().saturating_sub(1)));
        self.load_diff(same.is_none());
    }

    fn load_status(&mut self) {
        let st = self.git(&["status", "--porcelain=v2", "--branch", "-z", "--untracked-files=no"]).unwrap_or_default();
        self.parse_head(&st);
    }

    /// Branch name and the STATUS line (upstream, ahead/behind, any stopped operation)
    /// from porcelain v2 headers. True if there is a HEAD commit.
    fn parse_head(&mut self, st: &str) -> bool {
        let (mut oid, mut head, mut up, mut ab) = ("", "", None, None);
        for h in st.split('\0').filter_map(|r| r.strip_prefix("# ")) {
            match h.split_once(' ') {
                Some(("branch.oid", v)) => oid = v,
                Some(("branch.head", v)) => head = v,
                Some(("branch.upstream", v)) => up = Some(v),
                Some(("branch.ab", v)) => ab = Some(v),
                _ => {}
            }
        }
        let has_head = !oid.is_empty() && oid != "(initial)";
        self.branch = match head {
            "" | "(detached)" if has_head => oid[..7.min(oid.len())].to_string(),
            "" | "(detached)" => "(no commits)".into(),
            b => b.to_string(),
        };
        // No ahead/behind means the upstream is gone.
        self.status = match up.zip(ab) {
            Some((up, ab)) => {
                let mut s = format!("{} -> {up}", self.branch);
                let mut it = ab.split(' ').map(|n| &n[1..]);
                let (a, b) = (it.next().unwrap_or("0"), it.next().unwrap_or("0"));
                if a != "0" {
                    s += &format!(" ↑{a}");
                }
                if b != "0" {
                    s += &format!(" ↓{b}");
                }
                s
            }
            None => format!("{} (no upstream)", self.branch),
        };
        if let Some(op) = current_op(&self.root) {
            self.status += &format!(" ── {op} in progress, r to finish or abort");
        }
        has_head
    }

    fn load_entries(&mut self, st: &str, has_head: bool) {
        self.entries = status_entries(st);
        let base = if has_head { "HEAD" } else { EMPTY_TREE };
        let stats = numstat(&self.git(&["diff", base, "-M", "--numstat", "-z"]).unwrap_or_default());
        for e in &mut self.entries {
            e.stat = if e.x == b'?' {
                std::fs::read(self.root.join(&e.path))
                    .ok()
                    .filter(|b| !b.contains(&0))
                    .map(|b| (String::from_utf8_lossy(&b).lines().count(), 0))
            } else {
                stats.get(&e.path).copied().flatten()
            };
        }
        sort_entries(&mut self.entries);
    }

    /// Opens the history modal for `rev` (default: current branch), optionally one file's.
    fn open_history(&mut self, rev: Option<String>, file: Option<String>) {
        let old_rev = std::mem::replace(&mut self.hist_rev, rev);
        let old_file = std::mem::replace(&mut self.hist_file, file);
        // Show the last log for this at once, and load a fresh one behind it.
        let key = (self.hist_rev.clone(), self.hist_file.clone());
        if let Some(log) = self.log_cache.get(&key) {
            self.log = log.clone();
            self.start_log_load();
        } else {
            self.log = read_log(&self.root, key.0.as_deref(), key.1.as_deref());
            if self.log.is_empty() {
                (self.hist_rev, self.hist_file) = (old_rev, old_file);
                self.msg = "no commits".into();
                return;
            }
            self.log_cache.insert(key, self.log.clone());
        }
        self.mode = Mode::History;
        self.sel = 0;
        self.list_scroll = 0;
        self.query.clear();
        self.filter();
        self.start_fetch(Duration::from_secs(10));
    }

    /// Reads `log` for `hist_rev` and `hist_file`; false when there are no commits.
    fn start_log_load(&mut self) {
        let (tx, rx) = mpsc::channel();
        let (root, key) = (self.root.clone(), (self.hist_rev.clone(), self.hist_file.clone()));
        std::thread::spawn(move || {
            let log = read_log(&root, key.0.as_deref(), key.1.as_deref());
            _ = tx.send((key, log));
        });
        self.log_rx = Some(rx);
    }

    /// Takes a fresh log: cached, and shown if the history modal still lists it.
    fn finish_log(&mut self, key: LogKey, log: Vec<LogEntry>) {
        self.log_rx = None;
        if log.is_empty() {
            return;
        }
        self.log_cache.insert(key.clone(), log.clone());
        if self.mode == Mode::History && key == (self.hist_rev.clone(), self.hist_file.clone()) {
            let sha = self.log.get(self.sel).map(|c| c.sha.clone());
            self.log = log;
            self.sel = self.log.iter().position(|c| Some(&c.sha) == sha.as_ref()).unwrap_or(0);
            self.filter();
        }
    }

    fn open_files(&mut self) {
        let raw = self.git(&["ls-files", "-z"]).unwrap_or_default();
        self.files = raw.split('\0').filter(|f| !f.is_empty()).map(String::from).collect();
        self.mode = Mode::Files;
        self.list_scroll = 0;
        self.query.clear();
        self.filter();
    }

    fn open_branches(&mut self) {
        self.load_branches();
        self.mode = Mode::Branches;
        self.search_focus = true;
        self.list_scroll = 0;
        self.query.clear();
        self.filter();
        self.start_fetch(Duration::from_secs(10));
    }

    fn load_branches(&mut self) {
        let raw = self
            .git(&["for-each-ref", "--sort=-committerdate", "--format=%(refname)", "refs/heads", "refs/remotes"])
            .unwrap_or_default();
        self.branches = raw
            .lines()
            .filter(|r| !r.ends_with("/HEAD"))
            .filter_map(|r| {
                let local = r.strip_prefix("refs/heads/").map(|b| (b.to_string(), false));
                local.or_else(|| r.strip_prefix("refs/remotes/").map(|b| (b.to_string(), true)))
            })
            .collect();
    }

    /// Re-reads the open list modal after its refs changed, keeping the search and
    /// the selected row where it can.
    fn reload_list(&mut self) {
        match self.mode {
            Mode::Branches => {
                let pos = self.pos;
                self.load_branches();
                self.filter();
                self.move_to(pos);
            }
            Mode::History => self.start_log_load(),
            _ => {}
        }
    }

    /// Starts a background fetch unless one ran in the last `min_age` (or there's no remote).
    fn start_fetch(&mut self, min_age: Duration) {
        if self.fetching.is_some() || self.busy.is_some() || self.last_fetch.is_some_and(|t| t.elapsed() < min_age) {
            return;
        }
        self.last_fetch = Some(Instant::now());
        let (tx, rx) = mpsc::channel();
        let root = self.root.clone();
        std::thread::spawn(move || _ = tx.send(background_fetch(&root)));
        self.fetching = Some(rx);
    }

    fn finish_fetch(&mut self, moved: bool) {
        self.fetching = None;
        if moved {
            self.load_status();
            self.reload_list();
        }
        if let Some((steps, label, done)) = self.queued.take() {
            self.start_steps(steps, &label, &done);
        }
    }

    fn checkout(&mut self) {
        let Some(&i) = self.shown.get(self.pos) else { return };
        let res = match i {
            CREATE => self.git(&["switch", "-c", &self.query]),
            _ => match &self.branches[i] {
                (b, true) => self.git(&["switch", "--track", b]),
                (b, false) => self.git(&["switch", b]),
            },
        };
        match res {
            Ok(_) => {
                self.mode = Mode::Status;
                self.refresh();
                self.msg = format!("on {}", self.branch);
            }
            Err(err) => self.msg = err.lines().last().unwrap_or("checkout failed").to_string(),
        }
    }

    /// Recomputes `shown` from `query`. History keeps the selected commit when it
    /// still matches; branches offer a create row unless the query names a local branch.
    fn filter(&mut self) {
        let q = self.query.to_lowercase();
        if self.mode == Mode::Branches {
            self.shown = (0..self.branches.len()).filter(|&i| self.branches[i].0.to_lowercase().contains(&q)).collect();
            if !self.query.is_empty() && !self.branches.contains(&(self.query.clone(), false)) {
                self.shown.push(CREATE);
            }
            self.move_to(0);
            return;
        }
        if self.mode == Mode::Files {
            self.shown = (0..self.files.len()).filter(|&i| self.files[i].to_lowercase().contains(&q)).collect();
            self.move_to(0);
            return;
        }
        self.shown = (0..self.log.len())
            .filter(|&i| {
                let c = &self.log[i];
                [&c.sha, &c.date, &c.subject, &c.author].iter().any(|f| f.to_lowercase().contains(&q))
            })
            .collect();
        let pos = self.shown.iter().position(|&i| i == self.sel).unwrap_or(0);
        self.move_to(pos);
    }

    fn move_to(&mut self, pos: usize) {
        if self.shown.is_empty() {
            self.log_files.clear();
            return;
        }
        self.pos = pos.min(self.shown.len() - 1);
        if self.mode != Mode::History {
            return;
        }
        self.sel = self.shown[self.pos];
        match self.files_cache.get(&self.log[self.sel].sha) {
            Some(files) => self.log_files = files.clone(),
            None => {
                self.log_files.clear();
                self.start_files_load();
            }
        }
    }

    /// Loads the selected commit's files in the background, one commit at a time,
    /// so arrowing through history never waits on git.
    fn start_files_load(&mut self) {
        let Some(c) = self.log.get(self.sel) else { return };
        if self.files_rx.is_some() || self.files_cache.contains_key(&c.sha) {
            return;
        }
        let (tx, rx) = mpsc::channel();
        let (root, sha, parent) = (self.root.clone(), c.sha.clone(), c.parent.clone());
        std::thread::spawn(move || _ = tx.send((sha.clone(), commit_entries(&root, &sha, parent.as_deref()))));
        self.files_rx = Some(rx);
    }

    fn finish_files(&mut self, sha: String, files: Vec<Entry>) {
        self.files_rx = None;
        self.files_cache.insert(sha, files);
        if self.mode == Mode::History {
            self.move_to(self.pos);
        }
    }

    fn open_commit(&mut self) {
        let c = &self.log[self.sel];
        if !self.files_cache.contains_key(&c.sha) {
            self.log_files = commit_entries(&self.root, &c.sha, c.parent.as_deref());
            self.files_cache.insert(c.sha.clone(), self.log_files.clone());
        }
        self.mode = Mode::Commit;
        let entries = std::mem::replace(&mut self.entries, self.log_files.clone());
        self.saved = Some((entries, self.cur, std::mem::take(&mut self.diff), self.scroll));
        // Open on the file whose history this is; older commits may have it under another name.
        self.cur = self.entries.iter().position(|e| Some(&e.path) == self.hist_file.as_ref()).unwrap_or(0);
        self.load_diff(true);
    }

    fn select(&mut self, i: usize) {
        if i < self.entries.len() && i != self.cur {
            self.cur = i;
            self.load_diff(true);
        }
    }

    fn load_diff(&mut self, reset_scroll: bool) {
        self.diff = match self.entries.get(self.cur).cloned() {
            Some(e) => self.build_diff(&e),
            None => Diff::default(),
        };
        self.vis_width = 0;
        self.jump = reset_scroll.then(|| self.diff.rows.iter().position(|r| r.2).unwrap_or(0));
    }

    fn build_diff(&mut self, e: &Entry) -> Diff {
        let old_path = e.orig.as_deref().unwrap_or(&e.path);
        let show = |spec: String| git_bytes(&self.root, &["show", &spec]).ok();
        let (old, new) = if self.mode == Mode::Commit {
            let sha = &self.log[self.sel].sha;
            (show(format!("{sha}^:{old_path}")), show(format!("{sha}:{}", e.path)))
        } else if e.x == b'?' {
            (None, std::fs::read(self.root.join(&e.path)).ok())
        } else {
            (show(format!("HEAD:{old_path}")), std::fs::read(self.root.join(&e.path)).ok())
        };
        self.diff_of(old, new, &e.path)
    }

    fn diff_of(&mut self, old: Option<Vec<u8>>, new: Option<Vec<u8>>, path: &str) -> Diff {
        let (old, new) = (old.unwrap_or_default(), new.unwrap_or_default());
        if old.contains(&0) || new.contains(&0) {
            let l = || vec![Line::from("(binary file)")];
            return Diff { rows: vec![(Some(0), Some(0), false)], old: l(), new: l(), ..Default::default() };
        }
        let (old, new) = (String::from_utf8_lossy(&old), String::from_utf8_lossy(&new));

        let mut rows = vec![];
        let (mut del, mut ins) = (vec![], vec![]);
        fn flush(rows: &mut Vec<(Option<usize>, Option<usize>, bool)>, del: &mut Vec<usize>, ins: &mut Vec<usize>) {
            for k in 0..del.len().max(ins.len()) {
                rows.push((del.get(k).copied(), ins.get(k).copied(), true));
            }
            del.clear();
            ins.clear();
        }
        for op in TextDiff::from_lines(&old, &new).ops() {
            match *op {
                DiffOp::Equal { old_index, new_index, len } => {
                    flush(&mut rows, &mut del, &mut ins);
                    rows.extend((0..len).map(|k| (Some(old_index + k), Some(new_index + k), false)));
                }
                DiffOp::Delete { old_index, old_len, .. } => del.extend(old_index..old_index + old_len),
                DiffOp::Insert { new_index, new_len, .. } => ins.extend(new_index..new_index + new_len),
                DiffOp::Replace { old_index, old_len, new_index, new_len } => {
                    del.extend(old_index..old_index + old_len);
                    ins.extend(new_index..new_index + new_len);
                }
            }
        }
        flush(&mut rows, &mut del, &mut ins);

        // Highlighting a big file takes a noticeable time, so show it plain until it is done.
        let key = |text: &str| {
            let mut h = DefaultHasher::new();
            (path, text).hash(&mut h);
            h.finish()
        };
        let keys = (key(&old), key(&new));
        let (old_lines, new_lines) = match (self.lines_cache.get(&keys.0), self.lines_cache.get(&keys.1)) {
            (Some(o), Some(n)) => {
                self.hl_rx = None;
                (o.clone(), n.clone())
            }
            _ => {
                let (tx, rx) = mpsc::channel();
                let (ss, theme, path) = (self.ss.clone(), self.theme.clone(), path.to_string());
                let (o, n) = (old.to_string(), new.to_string());
                std::thread::spawn(move || {
                    _ = tx.send([(keys.0, highlight(&ss, &theme, &o, &path)), (keys.1, highlight(&ss, &theme, &n, &path))])
                });
                self.hl_rx = Some(rx);
                (plain(&old), plain(&new))
            }
        };
        Diff { rows, old: old_lines, new: new_lines, conflicts: vec![], keys }
    }

    fn finish_highlight(&mut self, [(ko, o), (kn, n)]: Highlighted) {
        self.hl_rx = None;
        if self.diff.keys == (ko, kn) {
            (self.diff.old, self.diff.new) = (o.clone(), n.clone());
            self.vis_width = 0;
        }
        // chisle: drop everything at a cap; LRU if revisits after the cap feel slow.
        if self.lines_cache.len() > 64 {
            self.lines_cache.clear();
        }
        self.lines_cache.insert(ko, o);
        self.lines_cache.insert(kn, n);
    }

    /// Side-by-side rows for a file with conflict markers: common lines on both sides,
    /// each conflict's left and right lines paired up.
    fn conflict_diff(&self, segs: &[Seg], path: &str) -> Diff {
        let (mut old, mut new, mut rows, mut conflicts) = (String::new(), String::new(), vec![], vec![]);
        let (mut oi, mut ni) = (0, 0);
        for seg in segs {
            match seg {
                Seg::Common(lines) => {
                    for l in lines {
                        old += l;
                        new += l;
                        rows.push((Some(oi), Some(ni), false));
                        oi += 1;
                        ni += 1;
                    }
                }
                Seg::Conflict(o, t) => {
                    let start = rows.len();
                    for k in 0..o.len().max(t.len()).max(1) {
                        rows.push(((k < o.len()).then_some(oi + k), (k < t.len()).then_some(ni + k), true));
                    }
                    old += &o.concat();
                    new += &t.concat();
                    oi += o.len();
                    ni += t.len();
                    conflicts.push((start, rows.len() - start));
                }
            }
        }
        Diff { rows, old: highlight(&self.ss, &self.theme, &old, path), new: highlight(&self.ss, &self.theme, &new, path), conflicts, ..Default::default() }
    }

    /// Runs `steps` in the background, showing `label…` meanwhile and `done` after.
    fn start_steps(&mut self, steps: Vec<Step>, label: &str, done: &str) {
        // Two gits fetching at once fight over ref locks.
        if self.fetching.is_some() {
            self.queued = Some((steps, label.into(), done.into()));
            self.msg = format!("{label} after the fetch…");
            return;
        }
        let (tx, rx) = mpsc::channel();
        let (root, done) = (self.root.clone(), done.to_string());
        std::thread::spawn(move || {
            let mut out = run_steps(&root, &steps);
            if out.res.is_ok() {
                out.res = Ok(done);
            }
            _ = tx.send(out);
        });
        self.busy = Some(rx);
        self.msg = format!("{label}…");
    }

    fn finish_steps(&mut self, out: Outcome) {
        self.refresh();
        self.reload_list();
        if out.rejected {
            let prompt = format!(
                "Push rejected: {} has commits your branch doesn't, e.g. after an amend or rebase. \
                 Force push replaces them with yours; it refuses if they changed since the last fetch.",
                self.git(&["rev-parse", "--abbrev-ref", "@{u}"]).unwrap_or("the remote branch".into()),
            );
            let yes = ("force push".into(), Action::ForcePush);
            let alt = Some(("pull (merge them in), then push".into(), Action::Sync));
            self.confirm = Some(Confirm { prompt, yes, alt });
            return;
        }
        if self.entries.iter().any(Entry::is_conflict) {
            self.pending = out.rest;
            self.stash_conflict = out.failed == Some(Step::StashPop);
            self.start_resolve();
            return;
        }
        if out.paused {
            self.pending = out.rest;
            self.after_resolved();
            return;
        }
        self.msg = out.res.unwrap_or_else(|e| e);
    }

    fn start_resolve(&mut self) {
        let files: Vec<String> = self.entries.iter().filter(|e| e.is_conflict()).map(|e| e.path.clone()).collect();
        if files.is_empty() {
            match current_op(&self.root) {
                Some(op) => {
                    let prompt = format!("The {op} is stopped with no conflicts left.");
                    let yes = (format!("continue the {op}"), Action::Continue);
                    let alt = Some((format!("abort the {op}, back to before it started"), Action::Abort));
                    self.confirm = Some(Confirm { prompt, yes, alt });
                }
                None => self.msg = "no conflicts".into(),
            }
            return;
        }
        self.mode = Mode::Resolve;
        self.msg.clear();
        let labels = (String::new(), String::new());
        self.resolve = Some(Resolve { files, file: 0, segs: None, labels, choices: vec![], cur: 0 });
        self.load_conflict();
    }

    fn load_conflict(&mut self) {
        let Some(r) = &self.resolve else { return };
        let path = r.files[r.file].clone();
        let text = std::fs::read(self.root.join(&path)).ok().map(|b| String::from_utf8_lossy(&b).into_owned());
        let (diff, segs, labels) = match text.as_deref().and_then(parse_conflicts) {
            Some((segs, left, right)) => (self.conflict_diff(&segs, &path), Some(segs), (left, right)),
            None => {
                let show = |stage: u8| git_bytes(&self.root, &["show", &format!(":{stage}:{path}")]).ok();
                let (ours, theirs) = (show(2), show(3));
                let mut d = self.diff_of(ours, theirs, &path);
                d.conflicts = vec![(0, d.rows.len())];
                (d, None, ("ours".into(), "theirs".into()))
            }
        };
        let r = self.resolve.as_mut().unwrap();
        r.choices = vec![None; diff.conflicts.len()];
        r.cur = 0;
        r.segs = segs;
        r.labels = labels;
        self.jump = Some(diff.conflicts.first().map_or(0, |c| c.0));
        self.diff = diff;
        self.vis_width = 0;
        self.cur = self.entries.iter().position(|e| e.path == path).unwrap_or(0);
    }

    /// Keeps the left or right side of the current conflict, or of all of them.
    fn choose(&mut self, left: bool, all: bool) {
        let Some(r) = self.resolve.as_mut() else { return };
        if all {
            r.choices.fill(Some(left));
        } else {
            r.choices[r.cur] = Some(left);
        }
        let n = r.choices.len();
        match (1..=n).map(|d| (r.cur + d) % n).find(|&k| r.choices[k].is_none()) {
            Some(k) => {
                r.cur = k;
                self.jump = Some(self.diff.conflicts[k].0);
                self.vis_width = 0;
            }
            None => self.finish_file(),
        }
    }

    /// Writes the chosen sides of the current file and stages it; then the next file.
    fn finish_file(&mut self) {
        let Some(r) = self.resolve.as_mut() else { return };
        let path = r.files[r.file].clone();
        let res = match &r.segs {
            Some(segs) => {
                let mut out = String::new();
                let mut k = 0;
                for seg in segs {
                    match seg {
                        Seg::Common(lines) => out += &lines.concat(),
                        Seg::Conflict(o, t) => {
                            out += &if r.choices[k] == Some(true) { o } else { t }.concat();
                            k += 1;
                        }
                    }
                }
                std::fs::write(self.root.join(&path), out)
                    .map_err(|e| e.to_string())
                    .and_then(|_| git(&self.root, &["add", "--", &path]))
            }
            None => {
                let (stage, side) = if r.choices[0] == Some(true) { (":2:", "--ours") } else { (":3:", "--theirs") };
                if git(&self.root, &["cat-file", "-e", &format!("{stage}{path}")]).is_ok() {
                    git(&self.root, &["checkout", side, "--", &path]).and_then(|_| git(&self.root, &["add", "--", &path]))
                } else {
                    git(&self.root, &["rm", "-q", "--", &path]) // that side deleted it
                }
            }
        };
        if let Err(err) = res {
            self.msg = git_err(&err);
            return;
        }
        r.file += 1;
        if r.file < r.files.len() {
            self.load_conflict();
        } else {
            self.after_resolved();
        }
    }

    /// Continues whatever stopped on conflicts, then any steps that were waiting on it.
    fn after_resolved(&mut self) {
        self.resolve = None;
        self.mode = Mode::Status;
        let mut res = self.continue_op();
        // rerere can resolve the next stop of a rebase on its own; keep going until
        // something needs a person or it finishes.
        for _ in 0..20 {
            if res.is_ok() || has_conflicts(&self.root) || !in_progress(&self.root) {
                break;
            }
            res = self.continue_op();
        }
        self.refresh();
        if self.entries.iter().any(Entry::is_conflict) {
            self.start_resolve(); // e.g. the next commit of a rebase
            return;
        }
        match res {
            Ok(m) if !self.pending.is_empty() => {
                let steps = std::mem::take(&mut self.pending);
                self.start_steps(steps, &m, "done");
            }
            Ok(m) => self.msg = m,
            Err(err) => {
                let stashed = self.pending.contains(&Step::StashPop);
                self.pending.clear();
                self.msg = git_err(&err) + if stashed { " (local changes still stashed)" } else { "" };
            }
        }
    }

    fn continue_op(&mut self) -> Result<String, String> {
        let gd = PathBuf::from(self.git(&["rev-parse", "--absolute-git-dir"])?);
        let cont = |op: &str| self.git(&["-c", "core.editor=true", op, "--continue"]).map(|_| format!("{op} continued"));
        if gd.join("rebase-merge").exists() || gd.join("rebase-apply").exists() {
            cont("rebase")
        } else if gd.join("MERGE_HEAD").exists() {
            self.git(&["commit", "--no-edit"]).map(|_| "merge committed".into())
        } else if gd.join("CHERRY_PICK_HEAD").exists() {
            cont("cherry-pick")
        } else if gd.join("REVERT_HEAD").exists() {
            cont("revert")
        } else if std::mem::take(&mut self.stash_conflict) {
            // A conflicted pop keeps the stash, and resolving staged its changes.
            self.git(&["stash", "drop"])?;
            self.git(&["reset", "-q"])?;
            Ok("stash applied".into())
        } else {
            Ok("conflicts resolved".into())
        }
    }


    fn toggle(&mut self) {
        let Some(e) = self.entries.get(self.cur) else { return };
        let mut paths = vec![e.path.as_str()];
        paths.extend(e.orig.as_deref());
        let cmd: &[&str] = if e.unstaged() {
            &["add", "-A", "--"]
        } else if self.git(&["rev-parse", "--verify", "-q", "HEAD"]).is_ok() {
            &["restore", "--staged", "--"]
        } else {
            &["rm", "--cached", "-q", "--"]
        };
        if let Err(err) = self.git(&[cmd, &paths].concat()) {
            self.msg = err;
        }
        self.refresh();
    }

    fn ask_undo(&mut self) {
        self.confirm = match self.mode {
            Mode::Status => self.entries.get(self.cur).map(|e| {
                let prompt = if e.x == b'?' {
                    format!("Delete untracked file {}?", e.path)
                } else {
                    format!("Discard all changes to {}, staged and unstaged?", e.path)
                };
                let label = if e.x == b'?' { "delete" } else { "discard" };
                let prompt = format!("{prompt} This cannot be undone.");
                Confirm { prompt, yes: (label.into(), Action::Discard(e.clone())), alt: None }
            }),
            Mode::Commit => {
                let c = &self.log[self.sel];
                let prompt = format!("Revert commit {} \"{}\"? This adds a new commit that undoes it.", c.short, c.subject);
                Some(Confirm { prompt, yes: ("revert".into(), Action::Revert(c.sha.clone())), alt: None })
            }
            _ => None,
        };
    }

    fn run_action(&mut self, action: Action) {
        let res = match &action {
            Action::Merge(rev) => {
                self.mode = Mode::Status;
                self.start_steps(vec![Step::Merge(rev.clone())], "merging", &format!("merged {rev}"));
                return;
            }
            Action::FetchMerge(remote, rref, tracking) => {
                self.mode = Mode::Status;
                let steps = vec![Step::Fetch(remote.clone(), rref.clone()), Step::Merge(tracking.clone())];
                self.start_steps(steps, "fetching", &format!("merged {tracking}"));
                return;
            }
            Action::ForcePush => {
                self.start_steps(vec![Step::ForcePush], "force pushing", "force pushed");
                return;
            }
            Action::Sync => {
                self.start_steps(vec![Step::Pull, Step::Push], "syncing", "synced");
                return;
            }
            Action::DeleteRemote(remote, name) => {
                self.start_steps(vec![Step::DeleteRemote(remote.clone(), name.clone())], "deleting", &format!("deleted {remote}/{name}"));
                return;
            }
            Action::DeleteBranch(b, force) => {
                self.delete_branch(b, *force);
                return;
            }
            Action::Continue => {
                self.after_resolved();
                return;
            }
            Action::Pause => {
                self.resolve = None;
                self.mode = Mode::Status;
                Ok("resolving paused; r to resume".into())
            }
            Action::Abort => self.abort(),
            Action::Discard(e) => self.discard(e),
            Action::Revert(sha) => {
                let mut args = vec!["revert", "--no-edit"];
                if self.git(&["rev-parse", "-q", "--verify", &format!("{sha}^2")]).is_ok() {
                    args.extend(["-m", "1"]); // merge: undo relative to the first parent
                }
                args.push(sha);
                // Conflicts or not, the result is in the working tree.
                self.mode = Mode::Status;
                self.git(&args).map(|_| format!("reverted {}", &sha[..7]))
            }
        };
        self.msg = res.unwrap_or_else(|e| git_err(&e));
        self.refresh();
    }

    /// Merges the highlighted branch into the current one. A local branch behind its
    /// upstream asks first, offering to fetch and merge the upstream instead.
    fn ask_merge(&mut self) {
        let Some((b, remote)) = self.shown.get(self.pos).and_then(|&i| self.branches.get(i)).cloned() else { return };
        if !remote && b == self.branch {
            self.msg = "can't merge a branch into itself".into();
            return;
        }
        if !remote
            && let Ok(up) = self.git(&[
                "for-each-ref",
                "--format=%(upstream:short)%00%(upstream:remotename)%00%(upstream:remoteref)",
                &format!("refs/heads/{b}"),
            ])
            && let [tracking, remote_name, rref] = up.split('\0').collect::<Vec<_>>()[..]
            && !tracking.is_empty()
        {
            let behind = self.git(&["rev-list", "--count", &format!("{b}..{tracking}")]).unwrap_or_default();
            let behind: usize = behind.trim().parse().unwrap_or(0);
            if behind > 0 {
                let prompt = format!("{b} is {behind} commit(s) behind {tracking}; those aren't pulled into {b}.");
                let yes = (format!("merge local {b} anyway"), Action::Merge(b.clone()));
                let fetch = Action::FetchMerge(remote_name.into(), rref.into(), tracking.into());
                self.confirm = Some(Confirm { prompt, yes, alt: Some((format!("fetch and merge {tracking}"), fetch)) });
                return;
            }
        }
        self.run_action(Action::Merge(b));
    }

    fn create_branch(&mut self) {
        let name = self.new_branch.clone().unwrap_or_default();
        let sha = self.log[self.sel].sha.clone();
        match self.git(&["switch", "-c", &name, &sha]) {
            Ok(_) => {
                self.new_branch = None;
                self.mode = Mode::Status;
                self.refresh();
                self.msg = format!("on {name}, from {}", &sha[..7]);
            }
            Err(err) => self.msg = git_err(&err),
        }
    }

    /// `d` in the branch list: a local branch goes if merged (else asks to force);
    /// a remote one asks first.
    fn ask_delete(&mut self) {
        let Some((b, remote)) = self.shown.get(self.pos).and_then(|&i| self.branches.get(i)).cloned() else { return };
        if !remote {
            self.delete_branch(&b, false);
            return;
        }
        let Some((r, name)) = b.split_once('/') else { return };
        let prompt = format!("Delete branch {name} from {r}? This removes it for everyone.");
        let yes = (format!("delete {b}"), Action::DeleteRemote(r.into(), name.into()));
        self.confirm = Some(Confirm { prompt, yes, alt: None });
    }

    fn delete_branch(&mut self, b: &str, force: bool) {
        if b == self.branch {
            self.msg = "can't delete the current branch".into();
            return;
        }
        match self.git(&["branch", if force { "-D" } else { "-d" }, b]) {
            Ok(_) => {
                self.msg = format!("deleted {b}");
                self.reload_list();
            }
            Err(err) if !force && err.contains("not fully merged") => {
                let prompt = format!("{b} isn't merged into {}. Delete it anyway? Commits no other branch has are lost.", self.branch);
                let yes = (format!("delete {b}"), Action::DeleteBranch(b.into(), true));
                self.confirm = Some(Confirm { prompt, yes, alt: None });
            }
            Err(err) => self.msg = git_err(&err),
        }
    }

    /// Leaving conflict resolution: pause by default, or abort the whole operation.
    fn ask_leave(&mut self) {
        let yes = ("pause; r resumes".into(), Action::Pause);
        let alt = match current_op(&self.root) {
            Some(op) => Some((format!("abort the {op}, back to before it started"), Action::Abort)),
            None if self.stash_conflict => Some(("stop applying the stash, keep it stashed".into(), Action::Abort)),
            None => None,
        };
        self.confirm = Some(Confirm { prompt: "Stop resolving conflicts?".into(), yes, alt });
    }

    fn abort(&mut self) -> Result<String, String> {
        self.resolve = None;
        self.mode = Mode::Status;
        let stashed = self.pending.contains(&Step::StashPop);
        self.pending.clear();
        let res = match current_op(&self.root) {
            Some(op) => self.git(&[op, "--abort"]).map(|_| format!("{op} aborted"))?,
            None if std::mem::take(&mut self.stash_conflict) => {
                self.git(&["reset", "--merge"])?;
                "stash not applied; it's still in git stash list".into()
            }
            None => "nothing to abort".into(),
        };
        // The sync stashed local changes before the aborted step; bring them back.
        if stashed {
            return match self.git(&["stash", "pop"]) {
                Ok(_) => Ok(format!("{res}, local changes restored")),
                Err(_) => Err(format!("{res} (local changes still stashed)")),
            };
        }
        Ok(res)
    }

    fn discard(&self, e: &Entry) -> Result<String, String> {
        if e.x == b'?' {
            std::fs::remove_file(self.root.join(&e.path)).map_err(|err| err.to_string())?;
        } else if self.git(&["cat-file", "-e", &format!("HEAD:{}", e.path)]).is_err() {
            self.git(&["rm", "-f", "-q", "--", &e.path])?;
        } else {
            self.git(&["restore", "--source=HEAD", "--staged", "--worktree", "--", &e.path])?;
        }
        // A rename also removed the old path; bring it back.
        if let Some(orig) = &e.orig {
            self.git(&["restore", "--source=HEAD", "--staged", "--worktree", "--", orig])?;
        }
        Ok(format!("discarded {}", e.path))
    }

    fn do_commit(&mut self) {
        let text = self.commit.clone().unwrap_or_default();
        let stage_all = !self.entries.iter().any(|e| e.staged());
        if stage_all {
            if let Err(err) = self.git(&["add", "-A"]) {
                self.msg = err;
                return;
            }
        }
        let res = match &self.amend {
            // An untouched subject keeps the whole message, body included.
            Some((subject, _)) if *subject == text => self.git(&["commit", "-q", "--amend", "--no-edit"]),
            Some(_) => self.git(&["commit", "-q", "--amend", "-m", &text]),
            None => self.git(&["commit", "-q", "-m", &text]),
        };
        if stage_all && res.is_err() {
            // Put the index back as it was.
            let undo: &[&str] = if self.git(&["rev-parse", "--verify", "-q", "HEAD"]).is_ok() {
                &["reset", "-q"]
            } else {
                &["rm", "-r", "--cached", "-q", "."]
            };
            _ = self.git(undo);
        }
        match res {
            Ok(_) => {
                self.msg = format!("{}: {text}", if self.amend.is_some() { "amended" } else { "committed" });
                self.commit = None;
                self.amend = None;
                self.refresh();
            }
            Err(err) => self.msg = err.lines().last().unwrap_or("commit failed").to_string(),
        }
    }

    /// Returns false to quit.
    fn key(&mut self, k: KeyEvent) -> bool {
        if self.busy.is_some() || self.queued.is_some() {
            if k.code == KeyCode::Char('c') && k.modifiers.contains(KeyModifiers::CONTROL) {
                return false;
            }
            return true;
        }
        if self.help {
            self.help = false;
            return true;
        }
        if self.confirm.is_some() {
            match k.code {
                KeyCode::Char('y') | KeyCode::Enter => {
                    if let Some(c) = self.confirm.take() {
                        self.run_action(c.yes.1);
                    }
                }
                KeyCode::Char('o') if self.confirm.as_ref().is_some_and(|c| c.alt.is_some()) => {
                    if let Some(Confirm { alt: Some((_, a)), .. }) = self.confirm.take() {
                        self.run_action(a);
                    }
                }
                KeyCode::Char('n') | KeyCode::Esc => self.confirm = None,
                _ => {}
            }
            return true;
        }
        if let Some(text) = &mut self.new_branch {
            match k.code {
                KeyCode::Esc => self.new_branch = None,
                KeyCode::Enter => self.create_branch(),
                KeyCode::Backspace => _ = text.pop(),
                KeyCode::Char(c) if !k.modifiers.contains(KeyModifiers::CONTROL) => text.push(c),
                _ => {}
            }
            return true;
        }
        if let Some(text) = &mut self.commit {
            match k.code {
                KeyCode::Esc => {
                    self.commit = None;
                    self.amend = None;
                }
                KeyCode::Enter => self.do_commit(),
                KeyCode::Tab => match self.amend.take() {
                    // Back to a new commit; drop the prefilled subject if it's untouched.
                    Some((subject, _)) => {
                        if *text == subject {
                            text.clear();
                        }
                    }
                    None => match git(&self.root, &["log", "-1", "--format=%s"]) {
                        Ok(subject) => {
                            let pushed = git(&self.root, &["merge-base", "--is-ancestor", "HEAD", "@{u}"]).is_ok();
                            if text.is_empty() {
                                *text = subject.clone();
                            }
                            self.amend = Some((subject, pushed));
                        }
                        Err(_) => self.msg = "no commit to amend".into(),
                    },
                },
                KeyCode::Backspace => _ = text.pop(),
                KeyCode::Char(c) if !k.modifiers.contains(KeyModifiers::CONTROL) => text.push(c),
                _ => {}
            }
            return true;
        }
        self.msg.clear();
        let ctrl = k.modifiers.contains(KeyModifiers::CONTROL);
        if self.mode == Mode::Branches {
            match k.code {
                KeyCode::Esc if self.search_focus => {
                    self.search_focus = false;
                    return true;
                }
                KeyCode::Char('/') if !self.search_focus => {
                    self.search_focus = true;
                    return true;
                }
                KeyCode::Char('m') if !self.search_focus => {
                    self.ask_merge();
                    return true;
                }
                KeyCode::Char('d') if !self.search_focus => {
                    self.ask_delete();
                    return true;
                }
                KeyCode::Char('?') if !self.search_focus => {
                    self.help = true;
                    return true;
                }
                KeyCode::Char('h') if !self.search_focus => {
                    if let Some((b, _)) = self.shown.get(self.pos).and_then(|&i| self.branches.get(i)).cloned() {
                        self.open_history(Some(b), None);
                    }
                    return true;
                }
                KeyCode::Char(c) if !self.search_focus && !(ctrl && c == 'c') => return true,
                _ => {}
            }
        }
        if matches!(self.mode, Mode::History | Mode::Branches | Mode::Files) {
            match k.code {
                KeyCode::Up => self.move_to(self.pos.saturating_sub(1)),
                KeyCode::Down => self.move_to(self.pos + 1),
                KeyCode::PageUp => self.move_to(self.pos.saturating_sub(self.list_page)),
                KeyCode::PageDown => self.move_to(self.pos + self.list_page),
                KeyCode::Home => self.move_to(0),
                KeyCode::End => self.move_to(usize::MAX),
                KeyCode::Enter if self.mode == Mode::Branches => self.checkout(),
                KeyCode::Enter if self.mode == Mode::Files => {
                    if let Some(&i) = self.shown.get(self.pos) {
                        self.open_history(None, Some(self.files[i].clone()));
                    }
                }
                KeyCode::Enter if !self.shown.is_empty() => self.open_commit(),
                KeyCode::Esc if !self.query.is_empty() => {
                    self.query.clear();
                    self.filter();
                }
                // The working tree view underneath is unchanged; the status poll catches up.
                KeyCode::Esc => self.mode = Mode::Status,
                KeyCode::Backspace => {
                    self.query.pop();
                    self.filter();
                }
                KeyCode::Char('c') if ctrl => return false,
                KeyCode::Char(c) if !ctrl => {
                    self.query.push(c);
                    self.filter();
                }
                _ => {}
            }
            return true;
        }
        if k.code == KeyCode::Char('q') || (k.code == KeyCode::Char('c') && k.modifiers.contains(KeyModifiers::CONTROL)) {
            return false;
        }
        let max = self.vis.len().saturating_sub(self.page);
        match (self.mode, k.code) {
            (Mode::Status, KeyCode::Esc) => return false,
            (Mode::Commit, KeyCode::Esc | KeyCode::Char('h')) => {
                self.mode = Mode::History;
                if let Some((entries, cur, diff, scroll)) = self.saved.take() {
                    (self.entries, self.cur, self.diff, self.scroll) = (entries, cur, diff, scroll);
                    self.vis_width = 0;
                }
            }
            (Mode::Status, KeyCode::Char('h')) => self.open_history(None, None),
            (Mode::Status, KeyCode::Char('H')) => match self.entries.get(self.cur) {
                Some(e) => self.open_history(None, Some(e.path.clone())),
                None => self.msg = "no file selected".into(),
            },
            (Mode::Status, KeyCode::Char('f')) => self.open_files(),
            (Mode::Status, KeyCode::Char('b')) => self.open_branches(),
            (Mode::Status | Mode::Commit, KeyCode::Char('u')) => self.ask_undo(),
            (Mode::Status, KeyCode::Char('p')) => self.start_steps(vec![Step::Pull], "pulling", "pulled"),
            (Mode::Status, KeyCode::Char('P')) => self.start_steps(vec![Step::Push], "pushing", "pushed"),
            (Mode::Status, KeyCode::Char('s')) => self.start_steps(vec![Step::Pull, Step::Push], "syncing", "synced"),
            (Mode::Commit, KeyCode::Char('b')) => self.new_branch = Some(String::new()),
            (Mode::Commit, KeyCode::Char('p')) => {
                let c = &self.log[self.sel];
                let (sha, done) = (c.sha.clone(), format!("cherry-picked {}", c.short));
                self.mode = Mode::Status;
                self.refresh();
                self.start_steps(vec![Step::CherryPick(sha)], "cherry-picking", &done);
            }
            (Mode::Status, KeyCode::Char('S')) => {
                let steps = if self.entries.is_empty() {
                    vec![Step::PullRebase, Step::Push]
                } else {
                    vec![Step::Stash, Step::PullRebase, Step::Push, Step::StashPop]
                };
                self.start_steps(steps, "stashing, rebasing, pushing", "synced");
            }
            (Mode::Status, KeyCode::Char('r')) => self.start_resolve(),
            (Mode::Status | Mode::Commit | Mode::Resolve, KeyCode::Char('v')) => {
                let i = LAYOUTS.iter().position(|l| l.0 == self.layout).unwrap_or(0);
                let (layout, value, name) = LAYOUTS[(i + 1) % LAYOUTS.len()];
                self.layout = layout;
                _ = self.git(&["config", "--global", "tit.layout", value]);
                self.msg = format!("layout: {name}");
                self.vis_width = 0;
            }
            (Mode::Status | Mode::Commit | Mode::Resolve, KeyCode::Char('e')) => {
                self.elide = !self.elide;
                _ = self.git(&["config", "--global", "tit.elide", &self.elide.to_string()]);
                self.msg = if self.elide { "hiding identical lines" } else { "showing whole file" }.into();
                self.vis_width = 0;
                self.jump = Some(self.diff.rows.iter().position(|r| r.2).unwrap_or(0));
            }
            (Mode::Resolve, KeyCode::Left) => self.choose(true, false),
            (Mode::Resolve, KeyCode::Right) => self.choose(false, false),
            (Mode::Resolve, KeyCode::Char('a')) => self.choose(true, true),
            (Mode::Resolve, KeyCode::Char('b')) => self.choose(false, true),
            (Mode::Resolve, KeyCode::Esc) => self.ask_leave(),
            (Mode::Status | Mode::Commit | Mode::Resolve, KeyCode::Char('?')) => self.help = true,
            (Mode::Status, KeyCode::Char(' ')) => self.toggle(),
            (Mode::Status, KeyCode::Enter) => self.commit = Some(String::new()),
            (_, code) => match code {
            KeyCode::Up => self.scroll = self.scroll.saturating_sub(1),
            KeyCode::Down => self.scroll += 1,
            KeyCode::PageUp => self.scroll = self.scroll.saturating_sub(self.page),
            KeyCode::PageDown => self.scroll += self.page,
            KeyCode::Home => self.scroll = 0,
            KeyCode::End => self.scroll = max,
            KeyCode::Left => self.select(self.cur.wrapping_sub(1)),
            KeyCode::Right => self.select(self.cur + 1),
            _ => {}
            },
        }
        self.scroll = self.scroll.min(max);
        true
    }

    /// Entries a commit would include: the staged ones, or all when none are staged.
    fn to_commit(&self) -> Vec<&Entry> {
        let staged: Vec<_> = self.entries.iter().filter(|e| e.staged()).collect();
        if staged.is_empty() { self.entries.iter().collect() } else { staged }
    }

    /// Renders `ents` (sorted) as the folder tree; `cur` is highlighted with its folders.
    /// `color` shows staged state; otherwise new files are green and deleted ones red.
    /// One line per folder, its files wrapped to `width` and aligned under the first.
    /// Also returns the line that holds `cur`.
    fn tree_lines(&self, ents: &[&Entry], cur: Option<&Entry>, color: bool, width: usize) -> (Vec<Line<'static>>, usize) {
        let cur_dirs = cur.map(|e| e.dirs());
        let ancestor = Style::new().fg(Color::Cyan).add_modifier(Modifier::BOLD);
        let mut lines = vec![];
        let mut prev: Option<Vec<&str>> = None;
        let mut cur_line = 0;
        let mut i = 0;
        while i < ents.len() {
            let dirs = ents[i].dirs();
            let j = i + ents[i..].iter().take_while(|e| e.dirs() == dirs).count();
            // Root is always shared after the first line; then any common leading dirs.
            let shared = prev.as_ref().map_or(0, |p| 1 + p.iter().zip(&dirs).take_while(|(a, b)| a == b).count());

            let mut spans = vec![];
            let segs = std::iter::once((self.root_name.as_str(), cur_dirs.is_some()))
                .chain(dirs.iter().enumerate().map(|(k, d)| (*d, cur_dirs.as_ref().is_some_and(|c| c.starts_with(&dirs[..=k])))));
            for (k, (seg, hl)) in segs.enumerate() {
                let hidden = k < shared;
                if k > 0 {
                    spans.push(Span::raw(if hidden { "   " } else { " / " }));
                }
                spans.push(if hidden {
                    Span::raw(" ".repeat(Span::raw(seg).width()))
                } else {
                    Span::styled(seg.to_string(), if hl { ancestor } else { Style::new() })
                });
            }
            spans.push(Span::raw(" / "));
            let indent = Line::from(spans.clone()).width();
            let mut used = indent;
            for (n, e) in ents[i..j].iter().enumerate() {
                let mut file = vec![];
                let mut st = match (color, e.staged(), e.unstaged()) {
                    _ if e.is_conflict() => Style::new().fg(Color::Magenta),
                    (true, true, false) => Style::new().fg(Color::Green),
                    (true, true, true) => Style::new().fg(Color::Yellow),
                    (false, ..) if e.is_new() => Style::new().fg(Color::Green),
                    (false, ..) if e.is_deleted() => Style::new().fg(Color::Red),
                    _ => Style::new(),
                };
                let is_cur = cur.is_some_and(|c| std::ptr::eq(c, *e));
                if is_cur {
                    st = st.add_modifier(Modifier::REVERSED | Modifier::BOLD);
                }
                file.push(Span::styled(e.name().to_string(), st));
                if let Some((add, del)) = e.stat {
                    if add > 0 {
                        file.push(Span::styled(format!(" +{add}"), Style::new().fg(Color::Green)));
                    }
                    if del > 0 {
                        file.push(Span::styled(format!(" -{del}"), Style::new().fg(Color::Red)));
                    }
                }
                let fw = Line::from(file.clone()).width();
                if n > 0 {
                    spans.push(Span::raw(","));
                    if used + 2 + fw > width {
                        lines.push(Line::from(std::mem::take(&mut spans)));
                        spans.push(Span::raw(" ".repeat(indent)));
                        used = indent;
                    } else {
                        spans.push(Span::raw(" "));
                        used += 2;
                    }
                }
                if is_cur {
                    cur_line = lines.len();
                }
                spans.extend(file);
                used += fw;
            }
            lines.push(Line::from(spans));
            prev = Some(dirs);
            i = j;
        }
        (lines, cur_line)
    }

    fn draw(&mut self, f: &mut Frame) {
        let a = f.area();
        let (w, h) = (a.width, a.height);
        if h < 4 {
            return;
        }
        let tree = |ents: &[Entry], cur: Option<&Entry>, empty: &str| {
            let (t, at) = self.tree_lines(&ents.iter().collect::<Vec<_>>(), cur, self.mode != Mode::Commit, (w as usize).saturating_sub(9));
            if t.is_empty() { vec![Line::from(empty.to_string())] } else { crop(t, at, (h as usize / 3).max(3)) }
        };
        let head = match self.mode {
            Mode::Status | Mode::History | Mode::Branches | Mode::Files => [
                labeled("STATUS", vec![Line::from(self.status.clone())]),
                labeled("BRANCH", vec![Line::from(self.branch.clone())]),
                labeled("CHANGE", tree(&self.entries, self.entries.get(self.cur), "(clean)")),
            ]
            .concat(),
            Mode::Resolve => {
                let r = self.resolve.as_ref().unwrap();
                let path = &r.files[r.file];
                let conflicts: Vec<Entry> = self.entries.iter().filter(|e| e.is_conflict()).cloned().collect();
                let at = format!("{path} ── conflict {} of {}", r.cur + 1, r.choices.len());
                [
                    labeled("RESOLV", vec![Line::from(at)]),
                    labeled("LEFT", vec![Line::from(r.labels.0.clone())]),
                    labeled("RIGHT", vec![Line::from(r.labels.1.clone())]),
                    labeled("FILES", tree(&conflicts, conflicts.iter().find(|e| e.path == *path), "")),
                ]
                .concat()
            }
            Mode::Commit => {
                let c = &self.log[self.sel];
                let files = tree(&self.entries, self.entries.get(self.cur), "(no changes)");
                [
                    labeled("COMMIT", vec![Line::from(vec![Span::styled(c.short.clone(), Style::new().fg(Color::Yellow)), Span::raw(format!(" {}", c.subject))])]),
                    labeled("AUTHOR", vec![Line::from(format!("{}, {}", c.author, c.date))]),
                    labeled("CHANGE", files),
                ]
                .concat()
            }
        };
        let hh = (head.len() as u16).min(h - 3);
        f.render_widget(Paragraph::new(head), Rect { height: hh, ..a });

        let lw = w.saturating_sub(1) / 2;
        let rw = w.saturating_sub(lw + 1);
        self.rewrap(w as usize);
        // Join the pane divider into the rules only when something is side by side.
        let split = self.vis.iter().any(|v| v.1.is_some());
        let mid = if split { lw } else { u16::MAX };
        let rule = |at: &[(u16, char)]| -> String {
            (0..w).map(|x| at.iter().find(|p| p.0 == x).map_or('─', |p| p.1)).collect()
        };
        f.render_widget(Paragraph::new(rule(&[(7, '┴'), (mid, '┬')])), Rect { y: hh, height: 1, ..a });
        f.render_widget(Paragraph::new(rule(&[(mid, '┴')])), Rect { y: h - 1, height: 1, ..a });
        // Messages in yellow; otherwise the few keys worth remembering, dimmed.
        let tips = match self.mode {
            Mode::Status => "space: stage, Enter: commit, ←→: file, h: history, b: branches, ?: help",
            Mode::Commit => "Esc: back, ←→: file, u: revert, p: cherry-pick, b: branch here, ?: help",
            Mode::Resolve => "←: keep left, →: keep right, a: all left, b: all right, Esc: pause/abort, ?: help",
            _ => "",
        };
        let (msg, color) = match self.msg.as_str() {
            "" => (tips, Color::DarkGray),
            m => (m, Color::Yellow),
        };
        if !msg.is_empty() {
            let m = Span::styled(format!(" {msg} "), Style::new().fg(color));
            f.render_widget(Paragraph::new(m), Rect { x: 1, y: h - 1, width: w.saturating_sub(2), height: 1 });
        }

        let y0 = hh + 1;
        let dh = h - hh - 2;
        self.page = (dh as usize).max(1);
        self.scroll = self.scroll.min(self.vis.len().saturating_sub(self.page));
        for (k, (l, r, lbg, rbg)) in self.vis.iter().skip(self.scroll).take(dh as usize).enumerate() {
            let y = y0 + k as u16;
            let full = Rect { x: 0, y, width: w, height: 1 };
            let (left, right) = match r {
                Some(_) => (Rect { width: lw, ..full }, Rect { x: lw + 1, width: rw, ..full }),
                None => (full, Rect { width: 0, ..full }),
            };
            if let Some(bg) = lbg {
                f.buffer_mut().set_style(left, Style::new().bg(*bg));
            }
            if let Some(bg) = rbg {
                f.buffer_mut().set_style(right, Style::new().bg(*bg));
            }
            f.render_widget(Paragraph::new(l.clone()), left);
            if let Some(r) = r {
                f.render_widget(Paragraph::new(r.clone()), right);
                f.render_widget(Paragraph::new("│"), Rect { x: lw, width: 1, ..full });
            }
        }

        if matches!(self.mode, Mode::History | Mode::Branches | Mode::Files) {
            let dim = Style::new().fg(Color::DarkGray);
            let (title, footer, items): (String, _, Vec<Line>) = match self.mode {
                Mode::History => {
                    let hist = self.log_files.iter().find(|e| Some(&e.path) == self.hist_file.as_ref());
                    // Width inside the modal border and label.
                    let fw = (w.saturating_sub(4).min(100) as usize).saturating_sub(11);
                    let mut files = self.tree_lines(&self.log_files.iter().collect::<Vec<_>>(), hist, false, fw).0;
                    if files.is_empty() {
                        files.push(Line::from("(no changes)"));
                    }
                    let items = self.shown.iter().map(|&i| {
                        let c = &self.log[i];
                        Line::from(vec![
                            Span::styled(c.short.clone(), Style::new().fg(Color::Yellow)),
                            Span::styled(format!(" {} ", c.date), Style::new().fg(Color::Blue)),
                            Span::raw(format!("{} ", c.subject)),
                            Span::styled(c.author.clone(), dim),
                        ])
                    });
                    let of = match (&self.hist_rev, &self.hist_file) {
                        (Some(r), _) => format!(" of {r}"),
                        (_, Some(f)) => format!(" of {f}"),
                        _ => String::new(),
                    };
                    (format!(" History{of} ── type to search, Enter: view, Esc: close "), labeled("FILES", files), items.collect())
                }
                Mode::Files => {
                    let items = self.shown.iter().map(|&i| {
                        let f = &self.files[i];
                        let (dir, name) = f.split_at(f.rfind('/').map_or(0, |k| k + 1));
                        Line::from(vec![Span::styled(dir.to_string(), dim), Span::raw(name.to_string())])
                    });
                    (" Files ── type to search, Enter: history, Esc: close ".into(), vec![], items.collect())
                }
                _ => {
                    let items = self.shown.iter().map(|&i| match i {
                        CREATE => Line::styled(format!("+ create branch '{}'", self.query), Style::new().fg(Color::Cyan)),
                        _ => match &self.branches[i] {
                            (b, true) => Line::styled(format!("  {b}"), Style::new().fg(Color::Blue)),
                            (b, false) if *b == self.branch => Line::styled(format!("* {b}"), Style::new().fg(Color::Green)),
                            (b, false) => Line::from(format!("  {b}")),
                        },
                    });
                    let title = if self.search_focus {
                    " Branches ── type to search or name a new branch, Enter: check out/create, Esc: done "
                } else {
                    " Branches ── /: search or new, Enter: check out, m: merge in, h: history, d: delete, ?: help "
                };
                (title.into(), vec![], items.collect())
                }
            };

            let pw = w.saturating_sub(4).min(100);
            let ph = h.saturating_sub(2);
            let r = Rect { x: (w - pw) / 2, y: (h - ph) / 2, width: pw, height: ph };
            f.render_widget(Clear, r);
            let block = Block::bordered().title(title);
            let inner = block.inner(r);
            f.render_widget(block, r);

            let search = labeled("SEARCH", vec![Line::from(self.query.clone())]);
            f.render_widget(Paragraph::new(search), Rect { height: 1, ..inner });
            let cx = inner.x + 9 + Span::raw(self.query.as_str()).width() as u16;
            if self.mode != Mode::Branches || self.search_focus {
                f.set_cursor_position(Position::new(cx.min(inner.right().saturating_sub(1)), inner.y));
            }
            f.render_widget(Paragraph::new(rule(&[(7, '┴')])), Rect { y: inner.y + 1, height: 1, ..inner });
            let list_area = Rect { y: inner.y + 2, height: inner.height.saturating_sub(2), ..inner };

            // The list gets what the footer leaves, but at least 3 rows.
            let full = list_area.height as usize;
            let lh = if footer.is_empty() { full } else { full.saturating_sub(footer.len() + 1).max(3).min(full) };
            self.list_page = lh.max(1);
            self.list_scroll = self.list_scroll.clamp((self.pos + 1).saturating_sub(self.list_page), self.pos);
            let mut list: Vec<Line> = items.into_iter().skip(self.list_scroll).take(lh).collect();
            if list.is_empty() {
                list.push(Line::styled("(no matches)", dim));
            }
            let lh = lh as u16;
            f.render_widget(Paragraph::new(list), Rect { height: lh, ..list_area });
            if !self.shown.is_empty() {
                let y = list_area.y + (self.pos - self.list_scroll) as u16;
                f.buffer_mut().set_style(Rect { y, height: 1, ..list_area }, Style::new().add_modifier(Modifier::REVERSED));
            }
            if !footer.is_empty() && lh < list_area.height {
                f.render_widget(Paragraph::new(rule(&[(7, '┬')])), Rect { y: list_area.y + lh, height: 1, ..list_area });
                let rest = Rect { y: list_area.y + lh + 1, height: list_area.height - lh - 1, ..list_area };
                f.render_widget(Paragraph::new(footer), rest);
            }
        }

        if let Some(text) = &self.commit {
            let pw = w.saturating_sub(4).min(80);
            let mut files = self.tree_lines(&self.to_commit(), None, false, (pw as usize).saturating_sub(11)).0;
            if files.is_empty() {
                files.push(Line::from("(message only)"));
            }
            let mut lines = labeled("FILES", files);
            lines.push(Line::from(rule(&[(7, '┴')])));
            if let Some((_, true)) = self.amend {
                lines.push(Line::styled("HEAD is already pushed: pushing the amend will need a force push", Style::new().fg(Color::Red)));
            }
            lines.push(Line::from(text.as_str()));
            let ph = (lines.len() as u16 + 2).min(h);
            let r = Rect { x: (w - pw) / 2, y: (h - ph) / 2, width: pw, height: ph };
            f.render_widget(Clear, r);
            let title = match self.amend {
                Some(_) => " Amend last commit ── Enter: amend, Tab: new commit instead, Esc: cancel ",
                None => " Commit ── Enter: commit, Tab: amend last commit, Esc: cancel ",
            };
            let block = Block::bordered().title(title);
            let skip = lines.len().saturating_sub(ph as usize - 2);
            f.render_widget(Paragraph::new(lines.split_off(skip)).block(block), r);
            let cx = (r.x + 1 + Span::raw(text.as_str()).width() as u16).min(r.right() - 2);
            f.set_cursor_position(Position::new(cx, r.bottom() - 2));
        }

        if let Some(c) = &self.confirm {
            let pw = w.saturating_sub(4).min(60);
            let text_w = (pw as usize).saturating_sub(2).max(1);
            let rows = Span::raw(c.prompt.as_str()).width().div_ceil(text_w) as u16;
            let red = Style::new().fg(Color::Red);
            let mut lines = vec![Line::from(c.prompt.as_str()), Line::default(), Line::styled(format!("y: {}", c.yes.0), red)];
            if let Some((label, _)) = &c.alt {
                lines.push(Line::styled(format!("o: {label}"), red));
            }
            lines.push(Line::styled("n / Esc: cancel", red));
            let ph = (rows + lines.len() as u16 + 1).min(h);
            let r = Rect { x: (w - pw) / 2, y: (h - ph) / 2, width: pw, height: ph };
            f.render_widget(Clear, r);
            let block = Block::bordered().border_style(red).title(" Confirm ");
            f.render_widget(Paragraph::new(lines).wrap(Wrap { trim: true }).block(block), r);
        }

        if let Some(text) = &self.new_branch {
            let pw = w.saturating_sub(4).min(60);
            let r = Rect { x: (w - pw) / 2, y: h / 2 - 1, width: pw, height: 3 };
            f.render_widget(Clear, r);
            let title = format!(" New branch from {} ── Enter: create, Esc: cancel ", self.log[self.sel].short);
            f.render_widget(Paragraph::new(text.as_str()).block(Block::bordered().title(title)), r);
            let cx = (r.x + 1 + Span::raw(text.as_str()).width() as u16).min(r.right() - 2);
            f.set_cursor_position(Position::new(cx, r.y + 1));
        }

        if self.help {
            let keys: &[(&str, &str)] = match self.mode {
                Mode::Status => &[
                    ("space", "stage / unstage file"),
                    ("Enter", "commit (Tab in the popup: amend last commit)"),
                    ("← →", "previous / next file"),
                    ("↑ ↓ PgUp PgDn", "scroll (Home / End: top / bottom)"),
                    ("u", "discard changes to file"),
                    ("h / H", "history of branch / of file"),
                    ("f", "project files, to see a file's history"),
                    ("b", "branches"),
                    ("p / P", "pull / push"),
                    ("s", "sync: pull, then push"),
                    ("S", "stash, pull --rebase, push, pop"),
                    ("r", "resolve conflicts, or finish / abort a stopped merge"),
                    ("e / v", "fold identical lines / cycle layout"),
                    ("q / Esc", "quit"),
                ],
                Mode::Commit => &[
                    ("← →", "previous / next file"),
                    ("↑ ↓ PgUp PgDn", "scroll (Home / End: top / bottom)"),
                    ("u", "revert this commit"),
                    ("p", "cherry-pick onto the current branch"),
                    ("b", "new branch from this commit"),
                    ("e / v", "fold identical lines / cycle layout"),
                    ("Esc / h", "back to history"),
                ],
                Mode::Resolve => &[
                    ("← / →", "keep left / right for this conflict"),
                    ("a / b", "keep left / right for all of this file"),
                    ("↑ ↓ PgUp PgDn", "scroll"),
                    ("e / v", "fold identical lines / cycle layout"),
                    ("Esc", "pause, or abort the whole operation"),
                ],
                _ => &[
                    ("/", "search, or type a new branch name"),
                    ("Enter", "check out (or create)"),
                    ("m", "merge into the current branch"),
                    ("h", "history of the branch"),
                    ("d", "delete (remote branches ask first)"),
                    ("Esc", "close"),
                ],
            };
            let kw = keys.iter().map(|k| Span::raw(k.0).width()).max().unwrap_or(0) + 3;
            let lines: Vec<Line> = keys
                .iter()
                .map(|(k, d)| Line::from(vec![Span::styled(format!(" {k:<kw$}"), Style::new().fg(Color::Cyan)), Span::raw(*d)]))
                .collect();
            let pw = w.saturating_sub(4).min(72);
            let ph = (lines.len() as u16 + 2).min(h);
            let r = Rect { x: (w - pw) / 2, y: (h - ph) / 2, width: pw, height: ph };
            f.render_widget(Clear, r);
            f.render_widget(Paragraph::new(lines).block(Block::bordered().title(" Keys ── any key closes ")), r);
        }
    }

    fn rewrap(&mut self, w: usize) {
        if self.vis_width == w {
            return;
        }
        self.vis_width = w;
        self.vis.clear();
        let lw = w.saturating_sub(1) / 2;
        let rw = w.saturating_sub(lw + 1);
        let dim = Style::new().fg(Color::DarkGray);
        // Line numbers, as wide as the largest one.
        let nw = self.diff.old.len().max(self.diff.new.len()).to_string().len();
        let num = |i: Option<usize>| i.map_or(" ".repeat(nw), |i| format!("{:>nw$}", i + 1));
        // Side by side: one number column per pane.
        let side = |lines: &[Line<'static>], i: Option<usize>, width: usize| -> Vec<Line<'static>> {
            let Some(i) = i else { return vec![] };
            let mut out = wrap(&lines[i], width.saturating_sub(nw + 1));
            for (k, l) in out.iter_mut().enumerate() {
                let prefix = if k == 0 { format!("{} ", num(Some(i))) } else { " ".repeat(nw + 1) };
                l.spans.insert(0, Span::styled(prefix, dim));
            }
            out
        };
        // Full width: old and new number columns, then a -/+ marker.
        let unified = |line: &Line<'static>, o: Option<usize>, n: Option<usize>, mark: char| -> Vec<Line<'static>> {
            let gutter = 2 * nw + 4;
            let mut out = wrap(line, w.saturating_sub(gutter));
            for (k, l) in out.iter_mut().enumerate() {
                let prefix = if k == 0 { format!("{} {} {mark} ", num(o), num(n)) } else { " ".repeat(gutter) };
                l.spans.insert(0, Span::styled(prefix, dim));
            }
            out
        };
        // Conflict colors: kept side green, dropped side red, current amber, the rest grey.
        let conflict_bg = |row: usize| -> Option<(Color, Color)> {
            let r = self.resolve.as_ref()?;
            let k = self.diff.conflicts.iter().position(|&(s, l)| row >= s && row < s + l)?;
            Some(match r.choices[k] {
                Some(true) => (ADD_BG, DEL_BG),
                Some(false) => (DEL_BG, ADD_BG),
                None if k == r.cur => (CUR_BG, CUR_BG),
                None => (PENDING_BG, PENDING_BG),
            })
        };
        // When eliding, keep only rows within CONTEXT of a change. A lone hidden row
        // would cost as much as its marker, so it stays.
        let rows = &self.diff.rows;
        let mut keep = vec![!self.elide; rows.len()];
        for (i, _) in rows.iter().enumerate().filter(|(_, r)| self.elide && r.2) {
            keep[i.saturating_sub(CONTEXT)..=(i + CONTEXT).min(rows.len() - 1)].fill(true);
        }
        for i in 0..keep.len() {
            if !keep[i] && (i == 0 || keep[i - 1]) && keep.get(i + 1).is_none_or(|&k| k) {
                keep[i] = true;
            }
        }
        // Blocks are runs of shown rows between folds; the whole file when not eliding.
        // A block with any line changed in place (old and new paired) is side by side;
        // one of only pure inserts and deletes is full width. Resolving is always split.
        let fixed = match self.layout {
            _ if self.mode == Mode::Resolve => Some(true),
            Layout::Split => Some(true),
            Layout::Unified => Some(false),
            Layout::Hybrid => None,
        };
        let mut split = vec![fixed.unwrap_or(false); rows.len()];
        let mut i = 0;
        while fixed.is_none() && i < rows.len() {
            let j = i + keep[i..].iter().take_while(|&&k| k == keep[i]).count();
            if keep[i] && rows[i..j].iter().any(|r| r.2 && r.0.is_some() && r.1.is_some()) {
                split[i..j].fill(true);
            }
            i = j;
        }
        // A hidden run shows as one dashed fold line.
        let marker: VisRow = (Line::styled("┄".repeat(w), dim), None, None, None);
        let mut hidden = 0;
        let mut jump_to = None;
        // Full-width `+` lines of a change wait until its `-` lines are out, like git.
        let mut plus: Vec<VisRow> = vec![];
        for (row, &(o, n, changed)) in self.diff.rows.iter().enumerate() {
            if !(changed && keep[row] && !split[row]) {
                self.vis.append(&mut plus);
            }
            if !keep[row] {
                hidden += 1;
                continue;
            }
            if hidden > 0 {
                hidden = 0;
                self.vis.push(marker.clone());
            }
            if self.jump == Some(row) {
                jump_to = Some(self.vis.len());
            }
            if !split[row] {
                let full = |line, o, n, mark, bg| unified(line, o, n, mark).into_iter().map(move |l| (l, None, bg, None));
                match (o, n) {
                    (_, Some(j)) if !changed => self.vis.extend(full(&self.diff.new[j], o, n, ' ', None)),
                    _ => {
                        if let Some(i) = o {
                            self.vis.extend(full(&self.diff.old[i], o, None, '-', Some(DEL_BG)));
                        }
                        if let Some(j) = n {
                            plus.extend(full(&self.diff.new[j], None, n, '+', Some(ADD_BG)));
                        }
                    }
                }
                continue;
            }
            let l = side(&self.diff.old, o, lw);
            let r = side(&self.diff.new, n, rw);
            let (lc, rc) = conflict_bg(row).unwrap_or((DEL_BG, ADD_BG));
            let lbg = (changed && o.is_some()).then_some(lc);
            let rbg = (changed && n.is_some()).then_some(rc);
            for k in 0..l.len().max(r.len()) {
                self.vis.push((l.get(k).cloned().unwrap_or_default(), Some(r.get(k).cloned().unwrap_or_default()), lbg, rbg));
            }
        }
        self.vis.append(&mut plus);
        if hidden > 0 {
            self.vis.push(marker);
        }
        if self.jump.take().is_some() {
            self.scroll = jump_to.unwrap_or(0).saturating_sub(3);
        }
    }

    fn run(&mut self, term: &mut DefaultTerminal) -> std::io::Result<()> {
        let mut checked = Instant::now();
        let mut checking: Option<Receiver<(String, String)>> = None;
        loop {
            term.draw(|f| self.draw(f))?;
            let loading = self.log_rx.is_some() || self.files_rx.is_some() || self.hl_rx.is_some();
            let wait = if self.busy.is_some() || self.queued.is_some() || checking.is_some() || loading { 50 } else { 500 };
            // Handle every key already queued before drawing again, so held keys don't lag.
            let mut wait = Duration::from_millis(wait);
            while event::poll(wait)? {
                wait = Duration::ZERO;
                if let Event::Key(k) = event::read()?
                    && k.kind == KeyEventKind::Press
                    && !self.key(k)
                {
                    return Ok(());
                }
            }
            if let Some(rx) = &self.busy
                && let Ok(out) = rx.try_recv()
            {
                self.busy = None;
                self.finish_steps(out);
            }
            if let Some(rx) = &self.fetching
                && let Ok(moved) = rx.try_recv()
            {
                self.finish_fetch(moved);
            }
            if let Some(rx) = &self.log_rx
                && let Ok((key, log)) = rx.try_recv()
            {
                self.finish_log(key, log);
            }
            if let Some(rx) = &self.files_rx
                && let Ok((sha, files)) = rx.try_recv()
            {
                self.finish_files(sha, files);
            }
            if let Some(rx) = &self.hl_rx
                && let Ok(sides) = rx.try_recv()
            {
                self.finish_highlight(sides);
            }
            // A failed fetch (offline, no access) just waits for the next one.
            self.start_fetch(Duration::from_secs(300));
            // git status is slow on Windows, so the check runs off the UI thread.
            if let Some(rx) = &checking
                && let Ok((now, st)) = rx.try_recv()
            {
                checking = None;
                checked = Instant::now();
                if now != self.sig && self.mode == Mode::Status && self.busy.is_none() {
                    self.refresh_from(&st);
                }
            }
            if checking.is_none() && self.mode == Mode::Status && self.busy.is_none() && checked.elapsed() >= Duration::from_secs(1) {
                let (tx, rx) = mpsc::channel();
                let (root, paths) = (self.root.clone(), self.paths());
                std::thread::spawn(move || _ = tx.send(signature(&root, &paths)));
                checking = Some(rx);
            }
        }
    }

    fn paths(&self) -> Vec<String> {
        self.entries.iter().map(|e| e.path.clone()).collect()
    }
}

/// Changes when the repo state or any changed file does: branch, HEAD, upstream,
/// status, and each listed file's mtime and size.
// chisle: polling; switch to a file watcher if one git status per second is too slow.
/// Also returns the status output, which `refresh_from` takes.
fn signature(root: &Path, paths: &[String]) -> (String, String) {
    let st = git(root, &["status", "--porcelain=v2", "--branch", "-z", "--untracked-files=all"]).unwrap_or_default();
    (signature_of(root, &st, paths), st)
}

fn signature_of(root: &Path, st: &str, paths: &[String]) -> String {
    let mut sig = st.to_string();
    for p in paths {
        let m = std::fs::metadata(root.join(p)).ok();
        sig += &format!("{:?}", m.map(|m| (m.modified().ok(), m.len())));
    }
    sig
}

fn highlight(ss: &SyntaxSet, theme: &Theme, text: &str, path: &str) -> Vec<Line<'static>> {
    let name = path.rsplit('/').next().unwrap_or(path);
    let syntax = name
        .rsplit_once('.')
        .and_then(|(_, ext)| ss.find_syntax_by_extension(ext))
        .or_else(|| ss.find_syntax_by_extension(name))
        .or_else(|| text.lines().next().and_then(|l| ss.find_syntax_by_first_line(l)))
        .unwrap_or_else(|| ss.find_syntax_plain_text());
    let mut h = HighlightLines::new(syntax, theme);
    LinesWithEndings::from(text)
        .map(|l| {
            let spans = h.highlight_line(l, ss).unwrap_or_default();
            Line::from(
                spans
                    .into_iter()
                    .map(|(st, s)| Span::styled(s.trim_end_matches(['\n', '\r']).replace('\t', "    "), to_style(st)))
                    .collect::<Vec<_>>(),
            )
        })
        .collect()
}

/// `text` as unstyled lines, line for line as `highlight` gives them.
fn plain(text: &str) -> Vec<Line<'static>> {
    LinesWithEndings::from(text).map(|l| Line::from(l.trim_end_matches(['\n', '\r']).replace('\t', "    "))).collect()
}

/// Splits a line into pieces at most `width` columns wide.
fn wrap(line: &Line<'static>, width: usize) -> Vec<Line<'static>> {
    let mut out = vec![Line::default()];
    let mut w = 0;
    for span in &line.spans {
        let mut buf = String::new();
        for c in span.content.chars() {
            let cw = c.width().unwrap_or(0);
            if w > 0 && w + cw > width {
                if !buf.is_empty() {
                    out.last_mut().unwrap().spans.push(Span::styled(std::mem::take(&mut buf), span.style));
                }
                out.push(Line::default());
                w = 0;
            }
            buf.push(c);
            w += cw;
        }
        if !buf.is_empty() {
            out.last_mut().unwrap().spans.push(Span::styled(buf, span.style));
        }
    }
    out
}

/// Maps syntect colors to terminal colors. The "ansi" theme encodes palette
/// indices as alpha 0 (index in red) and the default color as alpha 1.
fn to_style(s: highlighting::Style) -> Style {
    let c = s.foreground;
    let fg = match c.a {
        0 => Color::Indexed(c.r),
        1 => Color::Reset,
        _ => Color::Rgb(c.r, c.g, c.b),
    };
    let mut st = Style::new().fg(fg);
    if s.font_style.contains(FontStyle::BOLD) {
        st = st.add_modifier(Modifier::BOLD);
    }
    if s.font_style.contains(FontStyle::ITALIC) {
        st = st.add_modifier(Modifier::ITALIC);
    }
    if s.font_style.contains(FontStyle::UNDERLINE) {
        st = st.add_modifier(Modifier::UNDERLINED);
    }
    st
}

fn main() -> Result<(), Box<dyn Error>> {
    match std::env::args().nth(1).as_deref() {
        Some("-V" | "--version") => {
            println!("tit {}", env!("CARGO_PKG_VERSION"));
            return Ok(());
        }
        Some("-h" | "--help") => {
            println!("{}\n\nUsage: tit\n\nRun it inside a git repository. Press ? for keys.", env!("CARGO_PKG_DESCRIPTION"));
            return Ok(());
        }
        _ => {}
    }
    let Ok(root) = git(Path::new("."), &["rev-parse", "--show-toplevel"]) else {
        eprintln!("tit: not inside a git repository. cd into one and run tit again.");
        std::process::exit(1);
    };
    let mut app = App::new(PathBuf::from(root));
    let mut term = ratatui::init();
    let res = app.run(&mut term);
    ratatui::restore();
    Ok(res?)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_conflicts_and_drops_base() {
        let text = "a\n<<<<<<< HEAD\nours1\n||||||| base\nold\n=======\ntheirs1\n>>>>>>> other\nb\n<<<<<<< HEAD\n=======\ntheirs2\n>>>>>>> other\nc\n";
        let (segs, left, right) = parse_conflicts(text).unwrap();
        assert_eq!((left.as_str(), right.as_str()), ("HEAD", "other"));
        let shape: Vec<_> = segs
            .iter()
            .map(|s| match s {
                Seg::Common(l) => format!("C{}", l.concat()),
                Seg::Conflict(o, t) => format!("X{}|{}", o.concat(), t.concat()),
            })
            .collect();
        assert_eq!(shape, ["Ca\n", "Xours1\n|theirs1\n", "Cb\n", "X|theirs2\n", "Cc\n"]);
        assert!(parse_conflicts("no markers\n").is_none());
    }

    #[test]
    fn crop_keeps_current_line_and_notes_hidden() {
        let lines: Vec<Line<'static>> = (0..10).map(|i| Line::from(i.to_string())).collect();
        let text = |ls: Vec<Line<'static>>| ls.iter().map(|l| l.to_string()).collect::<Vec<_>>();
        assert_eq!(text(crop(lines.clone(), 5, 4)), ["… 4 more", "4", "5", "… 4 more"]);
        assert_eq!(text(crop(lines.clone(), 0, 4)), ["0", "1", "2", "… 7 more"]);
        assert_eq!(text(crop(lines.clone(), 9, 4)), ["… 7 more", "7", "8", "9"]);
        assert_eq!(crop(lines, 0, 10).len(), 10);
    }

    #[test]
    fn parses_status_v2_entries() {
        let raw = "# branch.oid (initial)\0# branch.head main\0\
            1 .M N... 100644 100644 100644 aa aa a b.txt\0\
            2 R. N... 100644 100644 100644 aa aa R100 new name\0old name\0\
            u UU N... 100644 100644 100644 100644 aa bb cc c.txt\0\
            ? dir/new file\0";
        let got: Vec<_> = status_entries(raw).iter().map(|e| (e.path.clone(), e.orig.clone(), e.x, e.y)).collect();
        assert_eq!(got, [
            ("a b.txt".into(), None, b' ', b'M'),
            ("new name".into(), Some("old name".into()), b'R', b' '),
            ("c.txt".into(), None, b'U', b'U'),
            ("dir/new file".into(), None, b'?', b'?'),
        ]);
    }
}
