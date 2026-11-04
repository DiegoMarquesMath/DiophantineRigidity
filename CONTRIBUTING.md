# Contributing

Contributions should improve the correctness, auditability, or exposition of
formal mathematics. Please read [AGENTS.md](AGENTS.md) and the
[verification standard](docs/VERIFICATION.md) before working on proofs.

Work in focused branches. For each proposition, cite the paper label, write
its full Lean statement, specify every uniform parameter, and document
assumptions. Run `bash scripts/check.sh`, inspect the axiom audit and open a
reviewable pull request. Do not use unproved shortcuts or silently change
a theorem to match available Lean lemmas.

**Publication note:** The revised source manuscript is not included; never
commit private text or unpublished material without the author's approval.

The original [MahlerLean](https://github.com/DiegoMarquesMath/MahlerLean)
library is a dependency, not a subdirectory of this project.
