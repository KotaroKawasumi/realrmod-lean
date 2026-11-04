# Real RMod classification and stacking

Lean 4 formalization of the real reference model, classification of weakly pointed
fusion Pi-supercategories over the real numbers, and stacking on a fixed finite
group. The public declarations are in the namespace `RMod.BrundanEllis`.

The Lean sources are extracted without modification from commit
`0fdab699a692daf5a7f23a4aaed6d7c29c90cd3c` of the original Superfusion project,
dated 28 September 2026. The proof entry point is [Solution.lean](Solution.lean).
This package contains its 2,877 project source dependencies, including the entry
point, together with the specification and axiom checks.

## Mathematical scope

| Result | Declaration and implementation |
| --- | --- |
| Construct the real model and prove the Brauer–Wall reference property | `realRMod`, `real_isBrauerWallReference` in [Classification.lean](RMod/BrundanEllis/Classification.lean) |
| Reconstruct every category in the specified class from a twist | `reconstruction` in [Classification.lean](RMod/BrundanEllis/Classification.lean) |
| Characterize monoidal superequivalence by gauge equivalence | `equivalence_iff_gauge` in [Classification.lean](RMod/BrundanEllis/Classification.lean) |
| Choose associator coefficients in `{1, -1}` | `sign_reconstruction` in [Classification.lean](RMod/BrundanEllis/Classification.lean) |
| Construct the Deligne product and its diagonal completion | [StackingDeligne.lean](RMod/BrundanEllis/StackingDeligne.lean), [StackingStack.lean](RMod/BrundanEllis/StackingStack.lean) |
| Identify the categorical stack with the prescribed product of twists | `stack_pullback` in [StackingStackPullback.lean](RMod/BrundanEllis/StackingStackPullback.lean) |
| Construct the gauge quotient's commutative group, degree map and splitting | [StackingGroup.lean](RMod/BrundanEllis/StackingGroup.lean), [StackingSplit.lean](RMod/BrundanEllis/StackingSplit.lean) |

For a finite group `G`, the splitting has type

```lean
TwistClass G ≃* ((G →* Multiplicative (ZMod 8)) × SHReal G)
```

Here `SHReal G` is defined as the kernel of the degree map. The splitting preserves
the degree and the given kernel inclusion; no natural choice of splitting is
claimed. An identification with a bordism group is outside this release.
See [the interface conventions](docs/BRUNDAN_ELLIS_INTERFACE.md) for the category
structures and tensor signs.

## Build and use

Install [Lean through elan](https://lean-lang.org/install/manual/), then clone
this repository and build the proofs:

```sh
git clone https://github.com/KotaroKawasumi/realrmod-lean.git
cd realrmod-lean
lake exe cache get
LEAN_NUM_THREADS=1 lake build Solution
LEAN_NUM_THREADS=1 lake env lean -j1 -M6144 verification/StackingFinalChecks.lean
```

The toolchain is **Lean 4.31.0**. The unchanged `lake-manifest.json` pins mathlib
to `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` and records every dependency revision.
Keep the manifest to retain these versions. Mathlib's cache supplies dependency
artifacts; this package's proofs still need to be compiled.

`lake build` also selects `Solution`. The original package name `superfusion`,
dependency declarations and Lean options are retained. In particular, `-j1`
limits each Lean process to one worker. The project is substantial: its proof
sources contain approximately 1.34 million lines. A full build can be lengthy.

To access the proved declarations in a Lean file:

```lean
import Solution

#check RMod.BrundanEllis.realRMod
#check RMod.BrundanEllis.reconstruction
#check RMod.BrundanEllis.stack_pullback
#check RMod.BrundanEllis.stackingSplit
```

## Specification and verification

[Challenge.lean](Challenge.lean) is the historical specification used by the
Comparator. Its registered construction and proof holes intentionally contain
`sorry`. It is excluded from the default build and is not imported by the proof
library. Import `Solution` to use the completed constructions and theorems.

The September 2026 records cover all **48 registered targets: 24 theorems and
24 constructions**, including the categorical stacking comparison and all 1,024
finite reference hexagons. They record successful Lean builds, permitted-axiom
checks, and declaration comparison by a patched local Comparator. The permitted
axioms are `propext`, `Quot.sound`, and `Classical.choice`. Additional kernel replay
and NanoDa were not run; this is not a production Palomar verification claim.

For this extracted package, source identity, import completeness and packaging
checks have been performed. A clean build and axiom check of this new directory
have **not** been rerun. [Verification details](docs/VERIFICATION.md) distinguish
the historical results from the extraction checks and give reproduction commands.

## Source provenance

[SOURCE.json](SOURCE.json) records the original revision and the packaging changes.
[SOURCE_SHA256SUMS](SOURCE_SHA256SUMS) records the original bytes of every copied
source, configuration and historical record. Check these copies with:

```sh
shasum -a 256 -c SOURCE_SHA256SUMS
```

The extraction preserves all retained Lean files exactly. The Lake configuration
selects `Solution` by default and uses submodule globs for the retained libraries.
The original umbrella modules, development history, papers, generated binaries,
external data tables and unrelated experiments are omitted.

## License

Copyright 2026 Kotaro Kawasumi and the Superfusion contributors.

Licensed under the [Apache License, Version 2.0](LICENSE). Existing copyright
notices are preserved. Dependencies retain their own licenses.
