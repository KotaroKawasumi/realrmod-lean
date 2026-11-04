# Verification scope and reproduction

The proof sources in this package are exact copies from
`0fdab699a692daf5a7f23a4aaed6d7c29c90cd3c`. Historical verification of those sources
and validation of the extracted package are separate records.

## Fresh GCP rebuild on 4 November 2026 (UTC)

The public repository was cloned anonymously from GitHub and checked out at
[`d3cc66cb31a1120249b346dbdbe3d8d4ceeff907`](https://github.com/KotaroKawasumi/realrmod-lean/tree/d3cc66cb31a1120249b346dbdbe3d8d4ceeff907).
The project had **zero `.olean` files before compilation**. Pinned Mathlib
dependency artifacts were downloaded with `lake exe cache get`; no project
artifacts from an earlier build were reused.

| Check | Result |
| --- | --- |
| `lake build Solution` | Passed, 11,435 jobs; 7 h 17 min 22 s |
| `lake build Challenge` | Passed, 8,559 jobs; 13.32 s |
| First axiom query, `-M8192` | Stopped at the configured Lean memory limit; exit 134 |
| Axiom-only retry, `-M65536` | Passed in 5.16 s; all 52 expected declarations, in order and without duplicates |
| Permitted axioms | Only `propext`, `Quot.sound`, and `Classical.choice` |
| Source and build inputs | Clean Git tree; 2,885 copied-file checksums verified; configuration and compiler hashes unchanged |
| Dependencies after verification | All 10 pinned Git revisions matched and their working trees were clean |
| Comparator, additional kernel replay and NanoDa | Not rerun |

`Challenge` retains its intentional specification holes, so its log includes
`sorry` warnings. The proof library does not import it. The completed `Solution`
declarations passed the permitted-axiom audit.

The VM ran Ubuntu 24.04 on x86_64 with 12 vCPUs and 96 GiB of RAM. The toolchain
was Lean 4.31.0. Each compiler used `-j1`; a launcher executed the original Lean
binary with unchanged arguments and at most eight concurrent compiler processes.
Temporary slot reservations lowered concurrency during memory-intensive checks.
The initial build service's peak memory, including file cache, was 75.12 GiB.
The successful axiom query's maximum resident set was 8.12 GiB.

The 8 GiB axiom-query limit was insufficient when loading the completed package.
Only that query was repeated with a higher limit. No Lean source, build option,
dependency revision or compiler binary was changed, and the project was not
recompiled. The initial job's exit 134 and failed output are preserved; the
separate axiom retry exited 0. The combined outcome is recorded in `result.json`.

- [Combined result](../verification/gcp-20261104/result.json) and
  [environment and timings](../verification/gcp-20261104/run.json).
- [Full project build log](../verification/gcp-20261104/build.log) and
  [specification build log](../verification/gcp-20261104/challenge.log).
- [Successful axiom output](../verification/gcp-20261104/axiom-retry/axioms.log)
  and [audit of all 52 declarations](../verification/gcp-20261104/axiom-retry/axiom-audit.json).
- [Initial memory-limit failure](../verification/gcp-20261104/axioms.log),
  [concurrency adjustments](../verification/gcp-20261104/concurrency-adjustments.jsonl),
  and [final source/dependency audit](../verification/gcp-20261104/final-environment-audit.json).
- [Checksums of the distributed evidence](../verification/gcp-20261104/SHA256SUMS).

Subsequent publication changes add documentation and verification records. The
Lean sources, toolchain, manifest and Lake configuration remain identical to the
tested public commit.

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
three files above document the original run. The later package rebuild is
recorded separately in the GCP section above.

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

[SOURCE.json](../SOURCE.json) records these checks and links the subsequent GCP
build and axiom audit. The Comparator has not been rerun for this package.

## Rebuild the extracted package

Run from a fresh checkout with Lean available through elan. To reproduce the
recorded revision:

```sh
git checkout d3cc66cb31a1120249b346dbdbe3d8d4ceeff907
shasum -a 256 -c SOURCE_SHA256SUMS
lake exe cache get
LEAN_NUM_THREADS=1 lake build Solution
LEAN_NUM_THREADS=1 lake build Challenge
LEAN_NUM_THREADS=1 lake env lean -j1 -M65536 verification/StackingFinalChecks.lean
```

The last command prints dependencies for all 48 targets and the four reference
hexagon declarations. Check that all 52 expected names occur, each once and in
the order given by the file, and that the output lists only the three permitted
axioms. The historical axiom output provides a reference. `#print axioms` prints
dependencies; its process exit status alone does not enforce the permitted list.

`Challenge` is compiled separately for the specification check. Its registered
`sorry` holes are intentional and are not proof results. `Solution` does not
import `Challenge`.

These commands reproduce compilation and axiom inspection. A new Comparator
comparison, additional kernel replay and NanoDa remain outside this GCP record.
