# Abrikosov Lattices in the Unit Disk

This directory contains the manuscript for a solution of part (v) of
Vicențiu D. Rădulescu's 2006 *SIAM Review* Proposed Problem 06-006,
“Abrikosov Lattices in Superconductivity.” http://math.ucv.ro/~radulescu/articles/06-006.pdf

## Problem and result

For an integer `n >= 2`, let `z_1, ..., z_n` be points in the open unit disk.
The problem is to minimize the logarithmic renormalized energy

```text
E_n(z_1,...,z_n) = -pi [
    2 sum_{i<j} log|z_i-z_j|
    + sum_{i,j=1}^n log|1-z_i conjugate(z_j)|
].
```

Here, `n` is the number of points (or vortices). The paper proves that the
minimizers are exactly the centered regular `n`-gons, up to rotation and
relabeling, whose vertices have radius

```text
rho_n = ((n-1)/(3n-1))^(1/(2n)).
```

In particular, `rho_n` tends to `1` as `n` tends to infinity, so the
minimizing configurations approach the boundary of the disk.

The proof changes the sign of the energy and works with an equivalent
multiplicative maximization problem. It combines a Cauchy-kernel determinant
estimate, a weighted Vandermonde bound, a sharp scalar inequality, and the
equality case of Hadamard's inequality.

## Files

- `main.tex` — manuscript source
- `references.bib` — BibTeX bibliography
- `main.pdf` — compiled paper, when generated

The accompanying Lean 4 supplementary project contains a machine-checked
formalization of the sharp bound, the equality classification, and the limit
of `rho_n`.

## Reproducing the Lean verification

The supplementary Lean project is the directory containing
`lakefile.toml`, `lean-toolchain`, and `RomanianOpenProblemStrict.lean`.
It pins both Lean and Mathlib to version `v4.34.0-rc1`, so no global Lean
version needs to be selected manually.

1. Install [Git](https://git-scm.com/) and the
   [Elan Lean version manager](https://github.com/leanprover/elan). Elan
   supplies the `lake` command and installs the pinned Lean toolchain on
   demand.
2. Download or clone the complete supplementary project. Keep its directory
   structure intact, including `lake-manifest.json` and the
   `RomanianProblem/` helper-module directory.
3. Open a terminal in the supplementary project's root directory.
4. Compile and kernel-check the main verification file:

   ```sh
   lake env lean RomanianOpenProblemStrict.lean
   ```

   On the first run, Lake may download the pinned Lean toolchain, Mathlib,
   and cached dependencies. The command succeeds silently apart from
   informational output and the requested axiom reports, and it exits with
   status code `0`.

5. Optionally compile the entire local Lean library as an additional check:

   ```sh
   lake build
   ```

At the end of `RomanianOpenProblemStrict.lean`, three `#print axioms`
commands audit the principal results:

- `objective_le_upperBound` — the sharp upper bound;
- `objective_eq_upperBound_iff_regular` — classification of equality cases;
- `rho_tendsto_one` — convergence of the maximizing radius to one.

Their output should list only the standard foundational axioms `propext`,
`Classical.choice`, and `Quot.sound`. It should not contain `sorryAx` or any
custom axiom. This confirms that the declarations and all their dependencies
were accepted by Lean's kernel without unfinished proofs.

## Building the paper

With a TeX distribution containing `latexmk`, run this command from the
`RomanianProblemPaper` directory:

```sh
latexmk -pdf main.tex
```

To remove generated LaTeX build files, run:

```sh
latexmk -c
```

The document uses the standard `article` class and the `amsmath`, `amssymb`,
`amsthm`, `mathtools`, `geometry`, and `hyperref` packages.
