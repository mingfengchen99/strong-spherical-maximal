# Verification

Run these commands from the repository root with the pinned Lean toolchain and
Python 3.9 or newer:

```sh
lake exe cache get
python3 scripts/verify.py --check-snapshot
```

[`scripts/verify.py`](../scripts/verify.py) builds every default target, checks the
proof sources, and audits their transitive axiom dependencies. The approved
snapshot contains 104 proof modules and 1,444 named public source declarations.
The proof sources are in [`src/`](../src/); module names and imports are unchanged.

## Main theorem

[`audits/MainAudit.lean`](../audits/MainAudit.lean) checks both the original
`StrongSpherical.MainTheorem` and its expanded quantifiers. It also prints the
axiom dependencies of the final theorem and its immediate supporting results.
Run it directly after a successful build:

```sh
lake env lean -DautoImplicit=false audits/MainAudit.lean
```

Other files in `audits/` provide additional checks for intermediate estimates.
They can be run with the same command, replacing the audit filename.

## Audit scope

The verification script rejects placeholder and custom axiom tokens in the proof
sources after blanking nested comments and string literals. It generates a Lean
file containing `#print axioms` for named public source declarations: `def`,
`abbrev`, `theorem`, `lemma`, named `instance`, and `structure`. Only `propext`,
`Classical.choice`, and `Quot.sound` are allowed. Automatically generated
projections, recursors, and private declarations are checked transitively when
they occur in the dependencies of an audited declaration; they are not counted as
separate source declarations.

Declaration extraction follows the project's current layout: each module uses one
namespace, which may be reopened. If that layout changes, update the script as
well. Source scanning supplements Lean elaboration and axiom inspection; it is
not an independent proof checker.

Logs and the generated full audit are written to the ignored `.verification/`
directory. GitHub Actions runs the same verification after building the project.

## Reviewed source snapshot

[`verification/sources.sha256`](verification/sources.sha256) records the hashes of
the reviewed proof sources, with filenames relative to `src/`. Moving the files
into this directory did not change their contents or recorded hashes.
`--check-snapshot` requires an exact match. To verify
intentional changes or added modules, use `python3 scripts/verify.py` without that
option, review the changes, and then update the snapshot as appropriate. New proof
modules must be registered as default targets and libraries in `lakefile.toml`.
