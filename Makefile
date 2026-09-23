# Shallot + Lens — single verification entry point.
# Fail-fast order: cheap, high-signal steps first.

LAKE_ENV = command -v lake >/dev/null 2>&1 || . $$HOME/.elan/env;

.PHONY: verify verify-fast audit lean lake-test lean-pal regen check-drift scala diff json-suite macro-peg-diff counterexample-diff corpus-golden disksize clean

verify: audit lean lake-test check-drift scala diff json-suite macro-peg-diff counterexample-diff
	@echo "== make verify: ALL GREEN =="

# For mid-proof iteration: source audit + proofs only.
verify-fast: audit lean

audit:
	scripts/audit-source.sh

lean:
	cd lean && $(LAKE_ENV) lake build

lake-test:
	cd lean && $(LAKE_ENV) lake test

# PAL ∈ PEG (unconditional, standard axioms only), via the Kim–Park artifact (lean-pal/).
# Separate toolchain (v4.31.0 + Mathlib); downloads the Mathlib cache, so it is
# deliberately NOT part of `verify`.
lean-pal:
	cd lean-pal && $(LAKE_ENV) lake exe cache get && lake build

regen:
	scripts/regen.sh

check-drift:
	scripts/check-drift.sh

scala:
	cd scala && sbt -batch test

diff:
	scripts/diff-results.sh

json-suite:
	scripts/json-suite.sh

macro-peg-diff:
	scripts/macro-peg-diff.sh

counterexample-diff:
	scripts/counterexample-diff.sh

corpus-golden:
	scripts/corpus-golden.sh

disksize:
	scripts/disksize.sh

clean:
	cd lean && $(LAKE_ENV) lake clean
	cd scala && sbt -batch clean
