# Verification scope and reproduction

The proof sources in this package are exact copies from
`0fdab699a692daf5a7f23a4aaed6d7c29c90cd3c`. Historical verification of those sources
and validation of the extracted package are separate records.

## Historical results on 28 September 2026

The original run completed the 48 targets listed in [comparator.json](../comparator.json):
24 theorems and 24 constructions. The finite left and right reference hexagons
cover 512 cases each, and are used by the proved `stack_pullback` theorem.

| Check | Recorded result |
| --- | --- |
| Solution and dependencies | Lean build passed, 11,435 jobs |
| Challenge and public stacking theorem | Lean builds passed |
| All 48 targets and four reference hexagon declarations | Axiom audit passed |
| Permitted axioms | `propext`, `Quot.sound`, `Classical.choice` |
| Comparator statement/dependency comparison and axiom checks | Passed, exit 0 |
| Additional kernel replay and NanoDa | Not run |

The compact original records are retained without modification:

- [Run summary](../verification/historical/StackingCompletedVerification.json).
- [Actual axiom output](../verification/historical/StackingCompletedAxioms.log).
- [Audit of declaration names, order, count and permitted axioms](../verification/historical/StackingCompletedAxiomAudit.log).

The run used a patched local macOS Comparator. Its changes skipped the additional
kernel replay and NanoDa; treated already type-compared registered theorems as
registered dependencies; streamed export files; and used a dense expression index
to reduce memory. The theorem-dependency change retained fixed-definition/type
comparison and the complete Solution axiom scan. The recorded peak physical
footprint of the Comparator run was 3,200 MB. Ordinary Lean proof checking was
performed by the builds. The result is not an unmodified upstream Comparator,
Linux Landrun sandbox, or production Palomar attestation.

The summary retains hashes of the original detailed logs. Most of those logs and
the original Comparator runner are not distributed in this source package. The
three files above are historical evidence, not a claim that the extracted package
has been rebuilt.

## Extraction checks

The extraction keeps every project module transitively imported by `Solution`,
plus the original `Challenge.lean` and `verification/StackingFinalChecks.lean`.

- All 2,879 retained Lean files match the original Git blobs byte for byte.
- Import headers are read with Lean 4.31.0's own header parser. Every project
  dependency is present; `Challenge` is absent from the proof import closure.
- A comment-aware static scan of the proof closure finds no `sorry`, `admit`,
  new `axiom`, `sorryAx`, `native_decide`, `ofReduceBool`, `unsafe` or
  `implemented_by` tokens. This scan is not a substitute for kernel checking.
- The external import roots are Lean's `Init`, `Mathlib` and `Batteries`.
- The toolchain and dependency manifest are exact copies. The package name,
  dependency declarations and elaboration options remain unchanged. Only the
  default target and the two library globs are adjusted in `lakefile.toml`.
- File checksums, configuration syntax and documentation links are checked.

[SOURCE.json](../SOURCE.json) records these checks and explicitly marks the new
package's clean build, axiom check and Comparator rerun as not run.

## Rebuild the extracted package

Run from a fresh checkout with Lean available through elan:

```sh
shasum -a 256 -c SOURCE_SHA256SUMS
lake exe cache get
LEAN_NUM_THREADS=1 lake build Solution
LEAN_NUM_THREADS=1 lake env lean -j1 -M6144 verification/StackingFinalChecks.lean
```

The last command prints dependencies for all 48 targets and the four reference
hexagon declarations. Check that all 52 expected names occur, each once and in
the order given by the file, and that the output lists only the three permitted
axioms. The historical axiom output provides a reference. `#print axioms` prints
dependencies; its process exit status alone does not enforce the permitted list.

`Challenge` can be compiled separately with `lake build Challenge` when preparing
a Comparator comparison. Its registered `sorry` holes are intentional and are
not proof results. `Solution` does not import `Challenge`.

Rebuilding is recommended to establish that this smaller distribution is usable
on its own. It is not a prerequisite imposed by GitHub, and additional independent
checkers are not needed merely to publish the sources. Until the new build is
run, describe the package as an extraction of the historically verified sources.
