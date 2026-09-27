# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

tit is a minimalist, opinionated terminal UI for git. It is not a full git client: add a feature only when it is an everyday need, and prefer one obvious key over options.

## Commands

```sh
cargo build                                   # must build with no warnings
cargo test                                    # unit tests
cargo test parses_conflicts_and_drops_base    # one test
cargo install --path .                        # install the binary
```

Run it from inside any git repository; it finds the root with `git rev-parse --show-toplevel`.

### Testing the UI

It is a full-screen TUI, so test it headless in tmux against throwaway repos, never this repo:

```sh
tmux new-session -d -s tit -x 110 -y 20 -c <test-repo> <path-to>/target/debug/tit
tmux send-keys -t tit <keys>; tmux capture-pane -t tit -p
```

For network features, use a bare `origin.git` plus two clones, so one clone can push behind the other's back.

## Architecture

Everything is in `src/main.rs`: one `App` struct, `key()` for input, `draw()` for output, and `run()` as the event loop.

- **git via the CLI only.** No libgit2. All calls go through `git_cmd`, which sets `GIT_OPTIONAL_LOCKS=0` and `GIT_TERMINAL_PROMPT=0`, so git never prompts or fights the user's own git for locks.
- **Modes.** `Mode` (Status, History, Commit, Branches, Files, Resolve) picks what `key()` and `draw()` do. Branches, History and Files are modals over the diff screen. The commit popup, `Confirm` dialogs and the help overlay sit on top of any mode.
- **Confirm/Action.** Anything destructive builds a `Confirm` with a `yes` and optional `alt` (`o`) `Action`; `run_action` performs it. Add new destructive operations as an `Action` variant, not inline.
- **Network steps.** Pull, push, sync and similar are a `Vec<Step>` run on a background thread (`start_steps` → `run_steps` → `finish_steps`) with an mpsc receiver. `Outcome` reports conflicts (`paused`), a rejected push (`rejected`, which offers force push) and the steps left to run after conflicts are resolved (for example the stash pop in `S`).
- **Background fetch.** `start_fetch` runs on a timer and when opening the branch and history modals. It uses ssh `BatchMode` so it never prompts. Steps started during a fetch are held in `queued` until it ends. Force push uses `--force-with-lease --force-if-includes`, so a background fetch cannot make an unsafe force push pass.
- **Stopped operations.** `current_op` reads the git-dir markers (rebase-merge, MERGE_HEAD, ...). Resolve mode walks conflicted files; `r` resumes it, and Esc offers pause or abort.
- **Diff pipeline.** `diff_of` uses `similar` for line rows, `highlight` applies syntect (themes and syntaxes from two-face), and `rewrap` turns rows into screen lines (`VisRow`) for the current width, caching by width. Blocks with in-place changes show side by side; pure inserts and deletes show full width. Layout (`v`) and folding of identical lines (`e`) are saved in the global git config as `tit.layout` and `tit.elide`.
- **Refresh.** `refresh` reloads status and entries on a timer. Partial staging is deliberately not supported: a staged file that is edited again is re-staged in full.

## Conventions

- Every key must appear in the footer tips or the `?` help overlay for its mode; keep both in step with `key()`.
- User-facing messages say what happened and what to do next, in plain words, not raw git errors (see `git_err`).
