/-
Superfusion / GaugeChi / QuintEdges6

Milestone M13-2-6 of the abstract `(p, χ)` arc: **the two `@`-genre edges
`E16M` and `E18M`** (`docs/m13-design.md`), continuing `GaugeChi.QuintEdges5`
(17 of 21 edges landed there).

**`E16M` (`V2 → V7`, `t_{a+b+c,d,e}@a(bc)`, faces `PBC`/`S1`)**: the
`a(bc)`-respelling of `E13M`'s move. `V2 = ((a(bc))d)e = GQ2(a,b,c,d)
⊗_{D_{a+b+c+d}} F_{a+b+c+d,e}` unfolds to `(GBR(a,b,c) ⊗_{D_{a+b+c}}
F_{a+b+c,d}) ⊗_{D_{a+b+c+d}} F_{a+b+c+d,e}` — the LITERAL `E13M`-template
shape (`QuintEdges3.lean`'s `gV1Assoc`/`gE13Step`) with `GBR Γ a b c` in
place of `GBL Γ a b c`: since `a+b+c` is a prefix cluster, a single
cast-free `RelTensor.assoc` (`gV2Assoc`) already exposes `GBR(a,b,c)
⊗_{D_{a+b+c}} GBL(a+b+c,d,e)` — `GBR`'s own already-general coefficient
recast (`RouteBimod.lean`'s `Module ((Γ.D (p+q+r)).carrier)ᵐᵒᵖ (GBR Γ p q
r)`, needing no new instance) supplies the `M`-side of `RelTensor.assoc`
verbatim. The whiskering step is then the SAME signed `(a+b+c)`-slot
amplification of `gTCanon Γ (a+b+c) d e` used by `E13M` (`gCanonHphi4 K Γ
(a+b) c d e`, reused verbatim — it is about `gTCanon`'s own equivariance,
independent of the spectator module `M`), only keyed to `GBR.grading Γ a b
c` in place of `GBL.grading Γ a b c` (`GradedRightSMul (Γ.D (a+b+c)).grading
(GBR.grading Γ a b c)`, already public, `GaugeParity.lean`). Target `V7 =
(a(bc))(de) = GBR(a,b,c) ⊗_{D_{a+b+c}} GBR(a+b+c,d,e)` matches exactly — NO
new supercommutation fact needed, confirming the round's reuse discovery.

**`E18M` (`V5 → V11`, `t_{a,b+c+d,e}@b(cd)`, faces `PCD`/`S2`)**: the
`b(cd)`-respelling of `E15M`'s move. `V5 = (a(b(cd)))e = GQ4(a,b,c,d)
⊗_{D_{a+b+c+d}} F_{a+b+c+d,e}` unfolds to `(GBR(b,c,d) ⊗_{D_{b+c+d}}
F_{a,b+c+d}) ⊗_{D_{a+b+c+d}} F_{a+b+c+d,e}` — ALREADY the two-level
`(M ⊗ N) ⊗ P` shape `RelTensor.assoc` needs directly, UNLIKE `E15M`'s `V4 =
GQ3(a,b,c,d)` (three-level, needing `gq3Assoc`'s associator-peeling stage
`gV4AssocA` first): `GQ4`'s own second factor `GBR(b,c,d) ⊗_{D_{b+c+d}}
F_{a,b+c+d}` is directly `M ⊗_A N`-shaped with `M = GBR Γ b c d`. So `gV5Assoc`
needs only the `E15M`-template's LATTER two stages (`RelTensor.assoc` then
`QuintEdges3.lean`'s already-landed `gFourCast`/`gFourCast_midSlot`
four-letter recast device, at the SAME instantiation `w,x,y,z,v := a,b,c,d,e`
— reused verbatim, since `gFourCast` never touches the outer spectator `M`)
— no `gq3Assoc`-style stage, no new recast device: the task's anticipated
"variant device" is unnecessary. The whiskering is the middle-slot
amplification of `gTCanon Γ a (b+c+d) e` (`gCanonMidSlot`, reused verbatim
from `E15M`), keyed to `GBR.grading Γ b c d`. The closing step `gV11Assoc`
mirrors `E15M`'s `gV10Assoc` (a single cast-free `RelTensor.assoc`, since
`(b+c+d)+e = b+c+d+e` syntactically), with `GBR Γ b c d` as the spectator in
place of `GBL Γ b c d`. Target `V11 = a((b(cd))e) = GQ2(b,c,d,e) ⊗_{D_{bcde}}
F_{a,bcde}` matches exactly.

Both edges assemble as genuine `LinearEquiv`s (`E16Mequiv`/`E18Mequiv`),
giving `E_kM`/`E_kM_bijective` by simple projection — the same discipline as
`E13M`/`E15M`. Neither edge needed any new toolkit piece beyond
`QuintEdges3.lean`'s: the round's reuse discovery (Pentagon.lean's/
`QuintEdges3.lean`'s machinery reused verbatim at the `GBR`-respelled
instantiation) is confirmed for both `@`-genre edges landed this round.
-/
import Superfusion.GaugeChi.QuintEdges5

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)

attribute [local instance 500] leftModule rightModule

variable (a b c d e : G)

/-! ### Edge 16: `E16M : V2 → V7`, `t_{a+b+c,d,e}@a(bc)` (owning faces
`PBC`, `S1`) -/

/-- **`gV2Assoc`**: `V2`'s own re-association, exposing `GBR(a,b,c)
⊗_{D_{a+b+c}} GBL(a+b+c,d,e)` directly — a SINGLE, cast-free
`RelTensor.assoc` (the `gV1Assoc` template, `a+b+c` a prefix cluster,
`GBR Γ a b c` in place of `GBL Γ a b c`; `GBR`'s own already-general
coefficient recast, `RouteBimod.lean`, supplies the `M`-side instance
verbatim). -/
noncomputable def gV2Assoc : V2 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (a + b + c)).carrier (GBR Γ a b c) (GBL Γ (a + b + c) d e) :=
  RelTensor.assoc K (Γ.D (a + b + c)).carrier (Γ.D (a + b + c + d)).carrier
    (GBR Γ a b c) (FusionColumn (Γ.fuse (a + b + c) d)) (FusionColumn (Γ.fuse (a + b + c + d) e))

/-- The signed `(a+b+c)`-slot whiskering of `gTCanon Γ (a+b+c) d e`, landing
`V7`'s own `GBR(a+b+c,d,e)` factor — the `gE13Step` template, keyed to
`GBR.grading Γ a b c` in place of `GBL.grading Γ a b c` (`gCanonHphi4 K Γ
(a+b) c d e` reused verbatim: it is `gTCanon`'s own equivariance, independent
of the spectator module). -/
noncomputable def gE16Step :
    RelTensor K (Γ.D (a + b + c)).carrier (GBR Γ a b c) (GBL Γ (a + b + c) d e) ≃ₗ[K]
      RelTensor K (Γ.D (a + b + c)).carrier (GBR Γ a b c) (GBR Γ (a + b + c) d e) :=
  PentagonB.smapEquiv K (Γ.D (a + b + c)).grading (GBR.grading Γ a b c)
    (gTCanon K Γ (a + b + c) d e) (gParity K Γ (a + b + c) d e) (gCanonHphi4 K Γ (a + b) c d e)

/-- **`E16M`, as a `LinearEquiv`**: `gV2Assoc` then the signed `(a+b+c)`-slot
amplification. -/
noncomputable def E16Mequiv : V2 K Γ a b c d e ≃ₗ[K] V7 K Γ a b c d e :=
  (gV2Assoc K Γ a b c d e).trans (gE16Step K Γ a b c d e)

/-- **Edge 16** `E16M : V2 → V7`, `t_{a+b+c,d,e}@a(bc)` (owning faces `PBC`,
`S1`; presentation: `S1`, `gV2Assoc` then the whiskered `gTCanon Γ (a+b+c)
d e`). -/
noncomputable def E16M : V2 K Γ a b c d e →ₗ[K] V7 K Γ a b c d e :=
  (E16Mequiv K Γ a b c d e).toLinearMap

theorem E16M_bijective : Function.Bijective (E16M K Γ a b c d e) :=
  (E16Mequiv K Γ a b c d e).bijective

/-! ### Edge 18: `E18M : V5 → V11`, `t_{a,b+c+d,e}@b(cd)` (owning faces
`PCD`, `S2`) -/

/-- **`gV5Assoc`**: `V5`'s own re-association, exposing `GBR(b,c,d)
⊗_{D_{b+c+d}} GBL(a,b+c+d,e)` — a two-step composite (`RelTensor.assoc`
then `QuintEdges3.lean`'s already-landed `gFourCast` at `w,x,y,z,v :=
a,b,c,d,e`), with NO extra associator-peeling stage: unlike `V4`'s
`GQ3(a,b,c,d)` (three-level, needing `gq3Assoc` first, `E15M`'s
`gV4AssocA`), `V5`'s `GQ4(a,b,c,d) = GBR(b,c,d) ⊗_{D_{b+c+d}} F_{a,b+c+d}`
is ALREADY the two-level shape `RelTensor.assoc` needs directly — the
round's reuse discovery: `gFourCast`/`gFourCast_midSlot` apply verbatim
(they never touch the outer spectator `M`), `GBL Γ b c d` swapped for
`GBR Γ b c d`. -/
noncomputable def gV5Assoc : V5 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (b + c + d)).carrier (GBR Γ b c d) (GBL Γ a (b + c + d) e) :=
  (RelTensor.assoc K (Γ.D (b + c + d)).carrier (Γ.D (a + b + c + d)).carrier
      (GBR Γ b c d) (FusionColumn (Γ.fuse a (b + c + d))) (FusionColumn (Γ.fuse (a + b + c + d) e))).trans
    (RelTensor.mapEquivRight K (gFourCast K Γ a b c d e) (gFourCast_midSlot K Γ a b c d e))

/-- The signed `(b+c+d)`-slot (middle-slot) whiskering of `gTCanon Γ a
(b+c+d) e`, landing `V11`'s own `GBR(a,b+c+d,e)` factor — the `gE15Step`
template, keyed to `GBR.grading Γ b c d` in place of `GBL.grading Γ b c d`
(`gCanonMidSlot K Γ a (b+c+d) e` reused verbatim). -/
noncomputable def gE18Step :
    RelTensor K (Γ.D (b + c + d)).carrier (GBR Γ b c d) (GBL Γ a (b + c + d) e) ≃ₗ[K]
      RelTensor K (Γ.D (b + c + d)).carrier (GBR Γ b c d) (GBR Γ a (b + c + d) e) :=
  PentagonB.smapEquiv K (Γ.D (b + c + d)).grading (GBR.grading Γ b c d)
    (gTCanon K Γ a (b + c + d) e) (gParity K Γ a (b + c + d) e) (gCanonMidSlot K Γ a (b + c + d) e)

/-- **`gV11Assoc`**: `V11`'s own re-association, exposing `GBR(b,c,d)
⊗_{D_{b+c+d}} GBR(a,b+c+d,e)` directly — a SINGLE, cast-free
`RelTensor.assoc` (`(b+c+d)+e = b+c+d+e` syntactically, the `gV10Assoc`
template with `GBR Γ b c d` in place of `GBL Γ b c d`). -/
noncomputable def gV11Assoc : V11 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (b + c + d)).carrier (GBR Γ b c d) (GBR Γ a (b + c + d) e) :=
  RelTensor.assoc K (Γ.D (b + c + d)).carrier (Γ.D (b + c + d + e)).carrier
    (GBR Γ b c d) (FusionColumn (Γ.fuse (b + c + d) e)) (FusionColumn (Γ.fuse a (b + c + d + e)))

/-- **`E18M`, as a `LinearEquiv`**: `gV5Assoc` then the signed `(b+c+d)`-slot
amplification, then `gV11Assoc⁻¹`. -/
noncomputable def E18Mequiv : V5 K Γ a b c d e ≃ₗ[K] V11 K Γ a b c d e :=
  ((gV5Assoc K Γ a b c d e).trans (gE18Step K Γ a b c d e)).trans (gV11Assoc K Γ a b c d e).symm

/-- **Edge 18** `E18M : V5 → V11`, `t_{a,b+c+d,e}@b(cd)` (owning faces `PCD`,
`S2`; presentation: `S2`, `gV5Assoc` then the whiskered `gTCanon Γ a
(b+c+d) e` then `gV11Assoc⁻¹`). -/
noncomputable def E18M : V5 K Γ a b c d e →ₗ[K] V11 K Γ a b c d e :=
  (E18Mequiv K Γ a b c d e).toLinearMap

theorem E18M_bijective : Function.Bijective (E18M K Γ a b c d e) :=
  (E18Mequiv K Γ a b c d e).bijective

end GaugeChi

end Superfusion
