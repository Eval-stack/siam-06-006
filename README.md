# Romanian open problem: Lean supplementary project

This directory contains the Lean 4 and Mathlib formalization accompanying the
paper *Abrikosov Lattices in the Unit Disk*.  The main checked file is
`RomanianOpenProblemStrict.lean`.

The source project consists of:

- `RomanianOpenProblemStrict.lean`
- `RomanianProblem.lean`
- the `RomanianProblem/` helper-module directory
- `lakefile.toml`
- `lake-manifest.json`
- `lean-toolchain`
- this `README.md`

From this directory, verify the main development with:

```text
lake env lean RomanianOpenProblemStrict.lean
```

This command completed successfully with exit code 0.  At the end of the main
file, `#print axioms` for `objective_le_upperBound`,
`objective_eq_upperBound_iff_regular`, and `rho_tendsto_one` reports only
`propext`, `Classical.choice`, and `Quot.sound`; it reports no `sorryAx` or
custom axioms.

The generated `.lake/` directory is deliberately excluded by `.gitignore`.
It contains downloaded dependencies and build artifacts and can be regenerated
from `lake-manifest.json` and `lean-toolchain`.
