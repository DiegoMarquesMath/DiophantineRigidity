# Publish this as a **new** GitHub repository

This archive is an independent project; **do not unzip it inside the old
MahlerLean repository**. The new repository has its own Git history.

## First publication (macOS)

1. Extract `DiophantineRigidity.zip` to `~/Developer/DiophantineRigidity`.
2. Open Terminal:

```bash
cd ~/Developer/DiophantineRigidity
brew install gh                 # only if gh is not already installed
gh auth login                  # only if not already authenticated
bash scripts/publish_github.sh
```

The script initializes Git, creates the initial commit, creates the **public**
repo `DiegoMarquesMath/DiophantineRigidity`, and pushes `main`. It does not
modify, delete or move the old MahlerLean repository.

To publish privately instead, change `--public` to `--private` in the
publish script before running it.

**The manuscript is not published.** `paper/ATH_rev.tex` and
`paper/ATH_rev.pdf` are excluded by `.gitignore` and the explicit
file-by-file staging command.

## Local source setup (never commit without author approval)

```bash
cd ~/Developer/DiophantineRigidity
cp ~/Desktop/AuditoriaTH/ATH_rev.tex paper/
cp ~/Desktop/AuditoriaTH/ATH_rev.pdf paper/
bash scripts/check_source_hashes.sh
```

## First Lean verification

```bash
lake exe cache get
bash scripts/check.sh
```

If the toolchain is not installed, install elan from the official Lean
installation instructions before running these commands. CI will also
build the project in GitHub Actions once pushed.

## Move local, already-audited work safely

The existing Mac checkout `~/Developer/MahlerLeanATH` may contain
uncommitted Gate 01 material. Do **not** lose or publish it accidentally.
Keep that checkout untouched, and carry over only approved mathematical
changes to this new repository after reconciling the namespaces and source
contracts. Do not copy its `.git` or `.lake` directories.

## Keeping projects distinct

- `MahlerLean` — existing verified project, maintained separately.
- `DiophantineRigidity` — new formalization, its own package and history.
- The old package is imported from an exact commit in `lakefile.toml`.
- Public draft PR #4 in MahlerLean may be closed as superseded after the
  new repo has been created and checked. Do not delete useful work.
