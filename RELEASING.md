# Releasing

## First release (one-time)

Do these in order. Nothing is pushed or published yet.

1. **GitHub repo.** Create it and push `master`:
   ```sh
   gh repo create Jijjy/tit --public --source . --push \
     --description "A minimalist, opinionated terminal UI for git"
   gh repo edit --add-topic git,tui,terminal,rust,ratatui
   ```
   If the repo lives anywhere else, update `repository` in `Cargo.toml` first.

2. **README image.** Record a short GIF or screenshot of tit in a throwaway repo, for example with
   [vhs](https://github.com/charmbracelet/vhs). Commit it under `docs/` and link it from `README.md`.
   `docs/` is outside the `include` list, so it stays out of the crate.

3. **CI.** Add `.github/workflows/ci.yml` that runs on push and pull request, on `ubuntu-latest` and `macos-latest`:
   `cargo build --locked`, `cargo test --locked`, `cargo clippy --locked -- -D warnings`.
   Fix whatever clippy reports before turning on `-D warnings`.

4. **Platform check.** tit has only been run on Linux. Run it once on macOS. Decide whether Windows is
   supported; if not, say so in `README.md`.

5. **Prebuilt binaries.** Run `cargo dist init` ([cargo-dist](https://github.com/axodotdev/cargo-dist)).
   Pick Linux and macOS targets, the shell installer, and a Homebrew tap
   (needs an empty `Jijjy/homebrew-tap` repo). It writes a release workflow that runs on tag push, so
   commit it before tagging.

6. **crates.io.** Publishing is permanent: a version can be yanked but never deleted or re-uploaded,
   and the name `tit` stays claimed by this account.
   ```sh
   cargo login                  # token from https://crates.io/settings/tokens
   cargo publish --dry-run
   cargo publish
   ```

7. **Tag.** Pushing the tag starts the cargo-dist release workflow.
   ```sh
   git tag -a v0.1.0 -m "tit 0.1.0"
   git push origin v0.1.0
   ```

8. **AUR.** Publish two packages: `tit` builds from the crates.io tarball, `tit-bin` repackages the
   Linux binary from the GitHub release. Other distros only if someone asks.

## Every later release

1. Bump `version` in `Cargo.toml`, then run `cargo build` so `Cargo.lock` follows.
2. Check that `cargo build` has no warnings and that `cargo test` and `cargo clippy` pass.
3. Commit as `Release vX.Y.Z`.
4. Run `cargo publish --dry-run`, then `cargo publish`.
5. Tag `vX.Y.Z` and push the tag. cargo-dist builds the binaries and updates the Homebrew tap.
6. Update `pkgver` and checksums in both AUR packages.

## Known gaps

- One unit test (conflict parsing). The UI is tested by hand in tmux, as `CLAUDE.md` describes.
- No `CHANGELOG.md`. Start one at the first release after 0.1.0, or use GitHub release notes only.
