# Strong spherical maximal operator in Lean 4

A Lean 4 / mathlib formalization of the main strong spherical maximal inequality in
[Mingfeng Chen, *Sharp Lᵖ estimates for the strong spherical maximal operator*, arXiv:2609.32421v2](https://arxiv.org/abs/2609.32421v2).

The final theorem is proved in [`Main.lean`](src/Main.lean):

```lean
import Main

example : StrongSpherical.MainTheorem := StrongSpherical.main_theorem
```

For every dimension `n ≥ 4` and exponent `(n + 1) / (n - 1) < p ≤ ∞`, it gives a
finite constant, depending on `n` and `p`, that bounds the strong spherical maximal
operator in `Lᵖ` for every compactly supported continuous complex-valued input.
The operator uses normalized spherical measure and the supremum over all positive
diagonal dilation parameters. The conclusion includes measurability.
The expanded Lean statement is `StrongSpherical.strong_spherical_maximal_bound`.

The repository contains 104 proof modules (18,860 lines). The main proof includes
the oscillatory estimates, Lemma 3.2, Proposition 1.3, Lemma 1.4, the normal-frequency
decomposition, interpolation, summation, and the `p = ∞` endpoint. The precise scope
is the unchanged `MainTheorem` in [`Definitions.lean`](src/Definitions.lean); informal
remarks and bibliography in the paper are not separate formalization targets.

## Build

Install [Lean through elan](https://lean-lang.org/install/) and Python 3.9 or newer.
From the repository root, run:

```sh
lake exe cache get
python3 scripts/verify.py
```

The verification script builds all default targets, checks the proof sources for
placeholders and custom axiom declarations, audits the named public source
declarations transitively, and rechecks the original and expanded main theorem.
It uses only the Python standard library. Logs and a generated audit file go to
the ignored `.verification/` directory.

The underlying commands for a minimal build and main theorem audit are:

```sh
lake build
lake env lean -DautoImplicit=false audits/MainAudit.lean
```

The versions are pinned in `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`:

| Dependency | Version |
| --- | --- |
| Lean | `leanprover/lean4:v4.32.0-rc1` |
| mathlib | `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56` |

The Lake manifest pins transitive dependencies and is kept under version control.
`lake exe cache get` downloads precompiled mathlib dependencies; an initial build
requires network access and several gigabytes of local disk space. `.lake/`
contains dependencies and build products and is excluded from Git.

## Read the proof

| Entry point | Content |
| --- | --- |
| [`Definitions.lean`](src/Definitions.lean) | Measures, operators, critical exponent, original target |
| [`Quadratic1D.lean`](src/Quadratic1D.lean), [`ProductOscillation.lean`](src/ProductOscillation.lean) | One-dimensional and product oscillatory estimates |
| [`QuadraticGraphL2.lean`](src/QuadraticGraphL2.lean) | Lemma 3.2: quadratic graph `L²` estimate |
| [`LocalEstimate.lean`](src/LocalEstimate.lean) | Proposition 1.3: local maximal estimate |
| [`GlobalKernelEstimate.lean`](src/GlobalKernelEstimate.lean) | Lemma 1.4: estimate over all positive radii |
| [`NormalDecomposition.lean`](src/NormalDecomposition.lean), [`NormalSphereLimit.lean`](src/NormalSphereLimit.lean) | Actual frequency pieces and spherical-measure limit |
| [`NormalPieceInterpolation.lean`](src/NormalPieceInterpolation.lean) | Sharp `Lᵖ` estimates for the frequency pieces |
| [`NormalPieceSummation.lean`](src/NormalPieceSummation.lean), [`SphericalDomination.lean`](src/SphericalDomination.lean) | Summation and domination of the original spherical maximal operator |
| [`SphericalLInfinity.lean`](src/SphericalLInfinity.lean), [`SphericalLp.lean`](src/SphericalLp.lean), [`Main.lean`](src/Main.lean) | Endpoint, finite exponents, final theorem |

All 104 proof modules are in `src/`. Lake uses this source directory, so imports
such as `import Main` remain unchanged. The repository is organized as follows:

```text
src/                  Lean proof modules (start with Definitions.lean and Main.lean)
audits/               Lean axiom and theorem-type audit entry points
docs/README.md        Verification procedure and audit scope
docs/verification/    Reviewed proof-source SHA256 snapshot
scripts/verify.py     Portable local and CI verification
.github/workflows/   GitHub Actions configuration
```

## Verification and provenance

The final theorem's transitive axiom dependencies are exactly `propext`,
`Classical.choice`, and `Quot.sound`. The verification script allows only these
standard Lean axioms. Source scanning complements the kernel's elaboration and
axiom checks; it is not an independent proof checker.

The approved source snapshot is recorded in
[`docs/verification/sources.sha256`](docs/verification/sources.sha256).
To verify that the 104 proof files still match that snapshot:

```sh
python3 scripts/verify.py --check-snapshot
```

The snapshot records this reviewed version. Future intentional proof changes can
be built and audited without `--check-snapshot`; update the snapshot only after
reviewing those changes. The default script derives its targets from the Lake
configuration, so new proof modules must be registered there.

GitHub Actions builds the project and runs the same audits on pushes and pull
requests.

See [`docs/README.md`](docs/README.md) for the verification procedure and audit scope.

## License

This repository intentionally does not include a project license at this stage.
Dependency licenses are provided by their respective projects; mathlib is licensed
under Apache-2.0.
