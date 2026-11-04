/-
Superfusion / GaugeChi / QuintExtract6

Milestone M13-R6b of the `(p, χ)` arc's CLUSTER-FACE phase, continuing
round R6 of `docs/m13-cluster-route.md` (the PBC face's PBC extraction
layer): completing the deferred pieces from `QuintExtract5.lean`
(`omegaPbcV4`, `omegaPbcV7`, `omegaPbcV2_mk`) plus the missing-leaf
deliverables (`E2M_leaf`, `E9M_leaf`, `E16M_general`) that only became
reachable once `omegaPbcV4`/`omegaPbcV7` land.

## What lands

* **`omegaPbcV4 : V4 ≃ₗ F_{b,c} ⊗ GQ2(a,b+c,d,e)`** — a `gblOuterCastV2`-mirror:
  `V4`'s own structure `((F_{b,c} ⊗ GBR Γ a (b+c) d) ⊗ F_{a+b+c+d,e})` (up to
  the DEFINITIONAL identity `GQ3Inner K Γ a b c d ≡ GBR Γ a (b+c) d`, since
  `(b+c)+d = b+c+d` syntactically) is peeled by a single cast-free
  `RelTensor.assoc` (`omegaPbcV4Step1`), landing `F_{b,c} ⊗ (GQ3Inner K Γ a
  b c d ⊗_{D_{a+b+c+d}} F_{a+b+c+d,e})`; the closing device `gq3v4Close`
  (mirroring `gblOuterCastV2`'s two-`RelTensor.lift`-leg construction
  VERBATIM, spelled throughout via `GQ3Inner`'s own name, never the raw/
  `GBR`-unfolded form) casts this to the literal `GQ2 K Γ a (b + c) d e`,
  using `GQ3Inner`'s ALREADY-REGISTERED `D_{a+b+c+d}` recast instance
  (`Quint.lean`'s `instModuleGQ3InnerRecast4`) on the source side and
  `GBR`'s OWN pre-existing coefficient-recast instance (`RouteBimod.lean`,
  instantiated at `p,q,r := a,(b+c),d`, giving EXACTLY `D_{a+(b+c)+d}`) on
  the target side — bridged by `gq3v4RecastAgree`, the "double recast
  agreement" lemma (both actions reduce, via two layers of
  `Module.compHom`/`rightActionEnd`, to the SAME raw computation on
  `FusionColumn (Γ.fuse a (b+c+d))`, differing only by which composed
  `Γ.gaugeCast` reaches the shared natural total `D_{a+(b+c+d)}` —
  `add_assoc_four a b c d` directly vs. `pbcHeq a b c d` then
  `add_assoc a (b+c) d`, the SAME proposition by proof irrelevance, closed
  by `gaugeCast_trans'`). Plus `omegaPbcV4_mk`.
* **`omegaPbcV7 : V7 ≃ₗ F_{b,c} ⊗ GQ5(a,b+c,d,e)`** — a plain, cast-free
  `RelTensor.assoc` (`omegaPbcV7Step1`) peels `F_{b,c}` directly off
  `GBR Γ a b c`, landing `F_{b,c} ⊗ (F_{a,b+c} ⊗_{D_{a+b+c}} GBR Γ (a+b+c) d
  e)`; the closing device `gq5v7Close` needs a GENUINELY NEW device,
  `gGbrCastFst` (a `GBR`-mirror of `ChiCanon.lean`'s `gColumnCastFst`,
  casting `GBR`'s own FIRST argument by `subst`, one level up: `GBR Γ p q r
  ≃ₗ GBR Γ p' q r` for `p = p'`), plus its `aslot`-transport law
  `gGbrCastFst_aslot` (the mirror of `gColumnCastFst_xslot`, ALSO by
  `subst; rfl` — crucially this holds regardless of `GBR`'s own aslot
  action being Koszul-SIGNED internally, since `subst` transports the
  WHOLE instance uniformly, so the sign never needs to be unpacked).
  `gq5v7Close` is then built exactly like `gblOuterCastV2` (identity on the
  fixed first factor `F_{a,b+c}`, `gGbrCastFst K Γ d e (add_assoc a b c)`
  on the second), landing the literal `GQ5 K Γ a (b + c) d e`. Plus
  `omegaPbcV7_mk`.
* **`omegaPbcV2_mk`** — the missing leaf for `QuintExtract5.lean`'s
  `omegaPbcV2`, mirroring `omegaPbcV10_mk`'s proof shape verbatim (chase
  through `gq2Assoc_mk`, `RelTensor.assoc_mk`, `gq2rCastMapLeftV2_mk`,
  `gq2rCast_mk`, `gblOuterCastV2_mk`).
* **`E2M_leaf`**: `E2M`'s (`QuintEdges2.lean`) generator formula on a fully
  split `V2`-generator — a bare `RelTensor.map` of the `GE2`-role map at
  the FIXED datum `gt2Canon (gTCanon Γ a (b+c) d)`, so the leaf is a direct
  two-step chase (`RelTensor.map_mk` then `GE2_mk_of_mem`), no new toolkit.
* **`E16M_general`**: `E16M`'s (`QuintEdges6.lean`) generator formula on an
  `F_{b,c}`-only-keyed (opaque `Z`, opaque `n`) `V2`-generator — the
  `E11M_general`/`E14M_general` genre, "nearly free" per the referees
  (`gV2Assoc` then `gE16Step`'s own `smapEquiv`/`smap_mk_of_mem`).
* **`E9M_leaf`**: `E9M`'s (`QuintEdges.lean`) generator formula on a fully
  split `V10`-generator — a bare `RelTensor.map` of the `GE4`-role map at
  the shifted quadruple `(b,c,d,e)`, the `E4M`/`E20M`-genre two-step chase
  (`RelTensor.map_mk` then `GE4_mk_of_mem`).

## Deferred (deviation record)

**`E15M_leaf` and the PRE-ROUND GATE (`E15M`'s `gCanonMidSlot`-genre smap
key) are DEFERRED to the next round.** `E15M` (`QuintEdges3.lean`) is
structurally the hardest of the four missing leaves — three composed
stages (`gV4Assoc` itself a THREE-stage assembly through `gq3Assoc.symm`,
a plain associator, and the four-letter recast device `gFourCast`, THEN
`gE15Step`'s own signed `(b+c+d)`-slot amplification of `gTCanon Γ a
(b+c+d) e` via `gCanonMidSlot`, THEN `gV10Assoc.symm`) — genuinely deeper
than the other three (bare `RelTensor.map`/`smap` wraps). Round budget
after landing the two gating ω's, the mechanical `omegaPbcV2_mk` leaf, and
the three lighter edge leaves did not extend to also deriving and
kernel-checking `E15M`'s full generator formula and cross-checking its
smap key against `omegaPbcV4`'s/`omegaPbcV10`'s extracted presentations.
No obstruction was discovered; this is a pure budget deferral, flagged for
the immediate next round (which now has `omegaPbcV4`/`omegaPbcV10` both
available, unblocking it).
-/
import Superfusion.GaugeChi.QuintExtract5

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c d e : G)

attribute [local instance 500] leftModule rightModule

/-! ### `omegaPbcV4 : V4 ≃ₗ F_{b,c} ⊗ GQ2(a,b+c,d,e)` -/

section OmegaPbcV4

/-- Stage 1 of `omegaPbcV4`: a plain, cast-free `RelTensor.assoc`, peeling
`F_{b,c}` off `GQ3 K Γ a b c d`'s own `GQ3Inner`-wrapped structure — `V4`'s
native shape `(F_{b,c} ⊗ GQ3Inner K Γ a b c d) ⊗ F_{a+b+c+d,e}` matches
`RelTensor.assoc`'s `(M ⊗[A] N) ⊗[B] P` directly, since `GQ3 K Γ a b c d :=
RelTensor D_{b+c} F_{b,c} (GQ3Inner K Γ a b c d)` and `V4`'s own outer
total instance (`instModuleGQ3Total`) is built on TOP of `GQ3Inner`'s
already-registered `D_{a+b+c+d}` recast (`instModuleGQ3InnerRecast4`). -/
noncomputable def omegaPbcV4Step1 : V4 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
      (RelTensor K (Γ.D (a + b + c + d)).carrier (GQ3Inner K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e))) :=
  RelTensor.assoc K (Γ.D (b + c)).carrier (Γ.D (a + b + c + d)).carrier
    (FusionColumn (Γ.fuse b c)) (GQ3Inner K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))

theorem omegaPbcV4Step1_mk (u : FusionColumn (Γ.fuse b c)) (m : GQ3Inner K Γ a b c d)
    (t : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    omegaPbcV4Step1 K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ3 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) (GQ3.mk K Γ a b c d u m) t)
      = RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
          (RelTensor K (Γ.D (a + b + c + d)).carrier (GQ3Inner K Γ a b c d)
            (FusionColumn (Γ.fuse (a + b + c + d) e))) u
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ3Inner K Γ a b c d)
            (FusionColumn (Γ.fuse (a + b + c + d) e)) m t) :=
  RelTensor.assoc_mk K (Γ.D (b + c)).carrier (Γ.D (a + b + c + d)).carrier
    (FusionColumn (Γ.fuse b c)) (GQ3Inner K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e)) u m t

/-- **`Γ.gaugeCast`'s inverse is the cast along the symmetric equality** —
the public generic version of `PentagonRouteMembership.lean`'s private
`gaugeCast_symm_apply`. -/
theorem gaugeCast_symm_apply' {x y : G} (h : x = y) (τ : (Γ.D y).carrier) :
    (Γ.gaugeCast h).toAlgEquiv.symm τ = (Γ.gaugeCast h.symm).toAlgEquiv τ :=
  Γ.gaugeCast_symm_apply h τ

/-- **The double-recast agreement, at the RAW `rightActionEnd` level,
across BOTH `Module.compHom` layers on EACH side at once**:
`instModuleGQ3InnerRecast4`'s single-layer `rightActionEnd` (`C :=
D_{a+b+c+d}` directly, using `instModuleFusionColumnRecast4` internally)
agrees with `GBR`'s own pre-existing coefficient-recast unfolded down to
ITS underlying NATURAL-total `rightActionEnd` (`C := D_{a+(b+c)+d}`,
`(b+c)+d = b+c+d` syntactically so this is literally the SAME `A`/`M`/`N`
as the LHS's), the coefficients related by composing `pbcHeq` then
`add_assoc a (b+c) d`, collapsing (proof irrelevance) to `add_assoc_four a
b c d`. Proved by induction on a FRESH raw `n`, mirroring `QuintEdges2.lean`'s
`GBR_abcd_natural_recast_smul_eq`; the `mk`-case needs BOTH
`fusionColumnRecast4_op_smul_def` (unfolding `instModuleFusionColumnRecast4`
down to `F_{a,(b+c+d)}`'s NATURAL action) and `gaugeCast_trans'`. -/
theorem gq3v4RecastFull (t : (Γ.D (a + b + c + d)).carrier)
    (n : RelTensor K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse (b + c) d))
      (FusionColumn (Γ.fuse a (b + c + d)))) :
    rightActionEnd K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse (b + c) d))
        (FusionColumn (Γ.fuse a (b + c + d))) (MulOpposite.op t) n
      = rightActionEnd K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse (b + c) d))
          (FusionColumn (Γ.fuse a (b + c + d)))
          (MulOpposite.op ((Γ.gaugeCast (add_assoc a (b + c) d)).toAlgEquiv
            ((Γ.gaugeCast (pbcHeq a b c d)).toAlgEquiv t))) n := by
  induction n using RelTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | mk v w =>
      rw [rightActionEnd_mk, rightActionEnd_mk, fusionColumnRecast4_op_smul_def, gaugeCast_trans']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **`gq3v4Close`, THE NEW DEVICE**: `GQ3Inner K Γ a b c d ⊗[D_{a+b+c+d}]
F_{a+b+c+d,e} ≃ GQ2 K Γ a (b+c) d e`, mirroring `gblOuterCastV2` VERBATIM
(two `RelTensor.lift` legs glued by `LinearEquiv.ofLinear`, identity on
the shared first factor, spelled throughout via `GQ3Inner`'s own name,
`gColumnCastFst` on the second) — the "double recast" from the round
brief, using `GQ3Inner`'s ALREADY-REGISTERED recast on the source and
`GBR`'s ALREADY-REGISTERED recast on the target, bridged by
`gq3v4RecastAgree` instead of a fresh instance. -/
private noncomputable def gq3v4CloseFwdBilin :
    GQ3Inner K Γ a b c d →ₗ[K] FusionColumn (Γ.fuse (a + b + c + d) e) →ₗ[K]
      GQ2 K Γ a (b + c) d e :=
  (RelTensor.mk K (Γ.D (a + (b + c) + d)).carrier (GBR Γ a (b + c) d)
    (FusionColumn (Γ.fuse (a + (b + c) + d) e))).compl₂
    (gColumnCastFst K Γ e (pbcHeq a b c d)).toLinearMap

private theorem gq3v4CloseFwdBilin_apply (m : GQ3Inner K Γ a b c d)
    (v : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    gq3v4CloseFwdBilin K Γ a b c d e m v
      = RelTensor.mk K (Γ.D (a + (b + c) + d)).carrier (GBR Γ a (b + c) d)
          (FusionColumn (Γ.fuse (a + (b + c) + d) e)) m
          (gColumnCastFst K Γ e (pbcHeq a b c d) v) := rfl

private theorem gq3v4CloseFwd_balanced :
    RelTensor.IsBalanced (Γ.D (a + b + c + d)).carrier (gq3v4CloseFwdBilin K Γ a b c d e) := by
  intro t m v
  rw [gq3v4CloseFwdBilin_apply, gq3v4CloseFwdBilin_apply, gColumnCastFst_xslot]
  show RelTensor.mk K (Γ.D (a + (b + c) + d)).carrier (GBR Γ a (b + c) d)
      (FusionColumn (Γ.fuse (a + (b + c) + d) e))
      (rightActionEnd K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse (b + c) d))
        (FusionColumn (Γ.fuse a (b + c + d))) (MulOpposite.op t) m)
      (gColumnCastFst K Γ e (pbcHeq a b c d) v)
    = RelTensor.mk K (Γ.D (a + (b + c) + d)).carrier (GBR Γ a (b + c) d)
        (FusionColumn (Γ.fuse (a + (b + c) + d) e)) m
        ((Γ.gaugeCast (pbcHeq a b c d)).toAlgEquiv t • gColumnCastFst K Γ e (pbcHeq a b c d) v)
  rw [gq3v4RecastFull]
  exact RelTensor.mk_op_smul K (Γ.D (a + (b + c) + d)).carrier (GBR Γ a (b + c) d)
    (FusionColumn (Γ.fuse (a + (b + c) + d) e)) ((Γ.gaugeCast (pbcHeq a b c d)).toAlgEquiv t) m
    (gColumnCastFst K Γ e (pbcHeq a b c d) v)

private noncomputable def gq3v4CloseFwd :
    RelTensor K (Γ.D (a + b + c + d)).carrier (GQ3Inner K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) →ₗ[K]
      GQ2 K Γ a (b + c) d e :=
  RelTensor.lift (gq3v4CloseFwdBilin K Γ a b c d e) (gq3v4CloseFwd_balanced K Γ a b c d e)

private theorem gq3v4CloseFwd_mk (m : GQ3Inner K Γ a b c d)
    (v : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    gq3v4CloseFwd K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ3Inner K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) m v)
      = RelTensor.mk K (Γ.D (a + (b + c) + d)).carrier (GBR Γ a (b + c) d)
          (FusionColumn (Γ.fuse (a + (b + c) + d) e)) m
          (gColumnCastFst K Γ e (pbcHeq a b c d) v) := by
  show RelTensor.lift (gq3v4CloseFwdBilin K Γ a b c d e) (gq3v4CloseFwd_balanced K Γ a b c d e)
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ3Inner K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) m v) = _
  rw [RelTensor.lift_mk, gq3v4CloseFwdBilin_apply]

private noncomputable def gq3v4CloseBwdBilin :
    GBR Γ a (b + c) d →ₗ[K] FusionColumn (Γ.fuse (a + (b + c) + d) e) →ₗ[K]
      RelTensor K (Γ.D (a + b + c + d)).carrier (GQ3Inner K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) :=
  (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ3Inner K Γ a b c d)
    (FusionColumn (Γ.fuse (a + b + c + d) e))).compl₂
    (gColumnCastFst K Γ e (pbcHeq a b c d)).symm.toLinearMap

private theorem gq3v4CloseBwdBilin_apply (m : GBR Γ a (b + c) d)
    (w : FusionColumn (Γ.fuse (a + (b + c) + d) e)) :
    gq3v4CloseBwdBilin K Γ a b c d e m w
      = RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ3Inner K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) m
          ((gColumnCastFst K Γ e (pbcHeq a b c d)).symm w) := rfl

private theorem gq3v4CloseBwd_balanced :
    RelTensor.IsBalanced (Γ.D (a + (b + c) + d)).carrier (gq3v4CloseBwdBilin K Γ a b c d e) := by
  intro s m w
  rw [gq3v4CloseBwdBilin_apply, gq3v4CloseBwdBilin_apply, gColumnCastFst_symm_xslot]
  have hbridge := gq3v4RecastFull K Γ a b c d ((Γ.gaugeCast (pbcHeq a b c d)).toAlgEquiv.symm s) m
  rw [AlgEquiv.apply_symm_apply] at hbridge
  show RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ3Inner K Γ a b c d)
      (FusionColumn (Γ.fuse (a + b + c + d) e))
      (rightActionEnd K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse (b + c) d))
        (FusionColumn (Γ.fuse a (b + c + d)))
        (MulOpposite.op ((Γ.gaugeCast (add_assoc a (b + c) d)).toAlgEquiv s)) m)
      ((gColumnCastFst K Γ e (pbcHeq a b c d)).symm w)
    = RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ3Inner K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) m
        ((Γ.gaugeCast (pbcHeq a b c d)).toAlgEquiv.symm s •
          (gColumnCastFst K Γ e (pbcHeq a b c d)).symm w)
  rw [← hbridge]
  exact RelTensor.mk_op_smul K (Γ.D (a + b + c + d)).carrier (GQ3Inner K Γ a b c d)
    (FusionColumn (Γ.fuse (a + b + c + d) e)) ((Γ.gaugeCast (pbcHeq a b c d)).toAlgEquiv.symm s) m
    ((gColumnCastFst K Γ e (pbcHeq a b c d)).symm w)

private noncomputable def gq3v4CloseBwd :
    GQ2 K Γ a (b + c) d e →ₗ[K]
      RelTensor K (Γ.D (a + b + c + d)).carrier (GQ3Inner K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) :=
  RelTensor.lift (gq3v4CloseBwdBilin K Γ a b c d e) (gq3v4CloseBwd_balanced K Γ a b c d e)

private theorem gq3v4CloseBwd_mk (m : GBR Γ a (b + c) d)
    (w : FusionColumn (Γ.fuse (a + (b + c) + d) e)) :
    gq3v4CloseBwd K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + (b + c) + d)).carrier (GBR Γ a (b + c) d)
          (FusionColumn (Γ.fuse (a + (b + c) + d) e)) m w)
      = RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ3Inner K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) m
          ((gColumnCastFst K Γ e (pbcHeq a b c d)).symm w) := by
  show RelTensor.lift (gq3v4CloseBwdBilin K Γ a b c d e) (gq3v4CloseBwd_balanced K Γ a b c d e)
      (RelTensor.mk K (Γ.D (a + (b + c) + d)).carrier (GBR Γ a (b + c) d)
        (FusionColumn (Γ.fuse (a + (b + c) + d) e)) m w) = _
  rw [RelTensor.lift_mk, gq3v4CloseBwdBilin_apply]

private theorem gq3v4CloseFwd_bwd :
    (gq3v4CloseFwd K Γ a b c d e).comp (gq3v4CloseBwd K Γ a b c d e) = LinearMap.id := by
  refine RelTensor.hom_ext fun m w => ?_
  show gq3v4CloseFwd K Γ a b c d e
      (gq3v4CloseBwd K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + (b + c) + d)).carrier (GBR Γ a (b + c) d)
          (FusionColumn (Γ.fuse (a + (b + c) + d) e)) m w))
    = RelTensor.mk K (Γ.D (a + (b + c) + d)).carrier (GBR Γ a (b + c) d)
        (FusionColumn (Γ.fuse (a + (b + c) + d) e)) m w
  rw [gq3v4CloseBwd_mk, gq3v4CloseFwd_mk, LinearEquiv.apply_symm_apply]

private theorem gq3v4CloseBwd_fwd :
    (gq3v4CloseBwd K Γ a b c d e).comp (gq3v4CloseFwd K Γ a b c d e) = LinearMap.id := by
  refine RelTensor.hom_ext fun m v => ?_
  show gq3v4CloseBwd K Γ a b c d e (gq3v4CloseFwd K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ3Inner K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) m v))
    = RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ3Inner K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) m v
  rw [gq3v4CloseFwd_mk, gq3v4CloseBwd_mk, LinearEquiv.symm_apply_apply]

noncomputable def gq3v4Close :
    RelTensor K (Γ.D (a + b + c + d)).carrier (GQ3Inner K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e))
      ≃ₗ[K] GQ2 K Γ a (b + c) d e :=
  LinearEquiv.ofLinear (gq3v4CloseFwd K Γ a b c d e) (gq3v4CloseBwd K Γ a b c d e)
    (gq3v4CloseFwd_bwd K Γ a b c d e) (gq3v4CloseBwd_fwd K Γ a b c d e)

theorem gq3v4Close_mk (m : GQ3Inner K Γ a b c d) (v : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    gq3v4Close K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ3Inner K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) m v)
      = RelTensor.mk K (Γ.D (a + (b + c) + d)).carrier (GBR Γ a (b + c) d)
          (FusionColumn (Γ.fuse (a + (b + c) + d) e)) m
          (gColumnCastFst K Γ e (pbcHeq a b c d) v) :=
  gq3v4CloseFwd_mk K Γ a b c d e m v

/-- **`gq3v4Close`'s `D_{b+c}`-slot equivariance, unconditional**: the
device only ever touches the SECOND factor, so it commutes freely with
`GQ3Inner`'s own outer-left `D_{b+c}`-action (`Pentagon.lean`'s
`leftModule`-supplied instance) — which is `rfl`-identical to `GBR Γ a
(b+c) d`'s own `bslot` action after unfolding both `Module.compHom`
layers, since `(b+c)+d = b+c+d` syntactically — so `leftActionEnd_mk`
applies on BOTH sides, closed by `exact` via defeq. -/
theorem gq3v4Close_bcSlot (y : (Γ.D (b + c)).carrier)
    (n : RelTensor K (Γ.D (a + b + c + d)).carrier (GQ3Inner K Γ a b c d)
      (FusionColumn (Γ.fuse (a + b + c + d) e))) :
    gq3v4Close K Γ a b c d e (y • n) = y • gq3v4Close K Γ a b c d e n := by
  induction n using RelTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | mk m v =>
      have hL : gq3v4Close K Γ a b c d e
          (y • RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ3Inner K Γ a b c d)
            (FusionColumn (Γ.fuse (a + b + c + d) e)) m v)
        = RelTensor.mk K (Γ.D (a + (b + c) + d)).carrier (GBR Γ a (b + c) d)
            (FusionColumn (Γ.fuse (a + (b + c) + d) e)) (y • m)
            (gColumnCastFst K Γ e (pbcHeq a b c d) v) := by
        rw [show (y • RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ3Inner K Γ a b c d)
              (FusionColumn (Γ.fuse (a + b + c + d) e)) m v
              : RelTensor K (Γ.D (a + b + c + d)).carrier (GQ3Inner K Γ a b c d)
                  (FusionColumn (Γ.fuse (a + b + c + d) e)))
            = RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ3Inner K Γ a b c d)
                (FusionColumn (Γ.fuse (a + b + c + d) e)) (y • m) v from
          leftActionEnd_mk K (Γ.D (a + b + c + d)).carrier (GQ3Inner K Γ a b c d)
            (FusionColumn (Γ.fuse (a + b + c + d) e)) y m v,
          gq3v4Close_mk]
      have hR : y • gq3v4Close K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ3Inner K Γ a b c d)
            (FusionColumn (Γ.fuse (a + b + c + d) e)) m v)
        = RelTensor.mk K (Γ.D (a + (b + c) + d)).carrier (GBR Γ a (b + c) d)
            (FusionColumn (Γ.fuse (a + (b + c) + d) e)) (y • m)
            (gColumnCastFst K Γ e (pbcHeq a b c d) v) := by
        rw [gq3v4Close_mk]
        exact leftActionEnd_mk K (Γ.D (a + (b + c) + d)).carrier (GBR Γ a (b + c) d)
          (FusionColumn (Γ.fuse (a + (b + c) + d) e)) y m
          (gColumnCastFst K Γ e (pbcHeq a b c d) v)
      rw [hL, hR]
  | add x y' hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]

/-- **`omegaPbcV4`**: `omegaPbcV4Step1` then `gq3v4Close` wrapped under the
outer `F_{b,c}` spectator (`RelTensor.mapEquivRight`) — landing the
literal, cast-free-in-the-`GBR`-slot `GQ2 K Γ a (b+c) d e`. -/
noncomputable def omegaPbcV4 : V4 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ2 K Γ a (b + c) d e) :=
  (omegaPbcV4Step1 K Γ a b c d e).trans
    (RelTensor.mapEquivRight K (gq3v4Close K Γ a b c d e) (gq3v4Close_bcSlot K Γ a b c d e))

/-- **The sign-free generator formula of `omegaPbcV4`.** -/
theorem omegaPbcV4_mk (u : FusionColumn (Γ.fuse b c)) (m : GQ3Inner K Γ a b c d)
    (t : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    omegaPbcV4 K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ3 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) (GQ3.mk K Γ a b c d u m) t)
      = RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ2 K Γ a (b + c) d e) u
          (GQ2.mk K Γ a (b + c) d e m (gColumnCastFst K Γ e (pbcHeq a b c d) t)) := by
  have h1 := omegaPbcV4Step1_mk K Γ a b c d e u m t
  show RelTensor.mapEquivRight K (gq3v4Close K Γ a b c d e) (gq3v4Close_bcSlot K Γ a b c d e)
      (omegaPbcV4Step1 K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ3 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) (GQ3.mk K Γ a b c d u m) t)) = _
  rw [h1]
  show RelTensor.map (LinearMap.id : FusionColumn (Γ.fuse b c) →ₗ[K] FusionColumn (Γ.fuse b c))
      (gq3v4Close K Γ a b c d e).toLinearMap (fun _ _ => rfl) (gq3v4Close_bcSlot K Γ a b c d e)
      (RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
        (RelTensor K (Γ.D (a + b + c + d)).carrier (GQ3Inner K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e))) u
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ3Inner K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) m t)) = _
  rw [RelTensor.map_mk, LinearMap.id_apply]
  simp only [LinearEquiv.coe_toLinearMap]
  rw [gq3v4Close_mk]
  rfl

end OmegaPbcV4

/-! ### `omegaPbcV7 : V7 ≃ₗ F_{b,c} ⊗ GQ5(a,b+c,d,e)` -/

section OmegaPbcV7

/-- Stage 1 of `omegaPbcV7`: a plain, cast-free `RelTensor.assoc`, peeling
`F_{b,c}` directly off `GBR Γ a b c` — `V7`'s own outer total instance
(`GBR`'s recast, `RouteBimod.lean`) is built through `F_{a,b+c}`'s already-
registered `D_{a+b+c}` recast (`Pentagon.lean`'s `fusionColumn_recast`
section), so no new instance is needed. -/
noncomputable def omegaPbcV7Step1 : V7 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
      (RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
        (GBR Γ (a + b + c) d e)) :=
  RelTensor.assoc K (Γ.D (b + c)).carrier (Γ.D (a + b + c)).carrier
    (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e)

theorem omegaPbcV7Step1_mk (u : FusionColumn (Γ.fuse b c)) (v : FusionColumn (Γ.fuse a (b + c)))
    (w : GBR Γ (a + b + c) d e) :
    omegaPbcV7Step1 K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c) (GBR Γ (a + b + c) d e)
          (GBR.mk Γ a b c u v) w)
      = RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
          (RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
            (GBR Γ (a + b + c) d e)) u
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
            (GBR Γ (a + b + c) d e) v w) :=
  RelTensor.assoc_mk K (Γ.D (b + c)).carrier (Γ.D (a + b + c)).carrier
    (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e) u v w

/-- **`gGbrCastFst`, THE NEW DEVICE**: casting `GBR`'s own FIRST argument
by `subst` — the `GBR`-mirror of `ChiCanon.lean`'s `gColumnCastFst`, one
level up (`GBR Γ p q r` in place of a plain fusion column). -/
noncomputable def gGbrCastFst (q r : G) {p p' : G} (h : p = p') :
    GBR Γ p q r ≃ₗ[K] GBR Γ p' q r := by
  subst h
  exact LinearEquiv.refl K _

/-- The untouched `q`-slot (`bslot`) commutes trivially with the cast. -/
theorem gGbrCastFst_bslot (q r : G) {p p' : G} (h : p = p')
    (y : (Γ.D q).carrier) (w : GBR Γ p q r) :
    gGbrCastFst K Γ q r h (y • w) = y • gGbrCastFst K Γ q r h w := by
  subst h
  rfl

/-- **The `aslot`-transport law**, the mirror of `gColumnCastFst_xslot`:
`GBR`'s own FIRST-argument (Koszul-signed) slot action transports along
`Γ.gaugeCast h` — this holds by `subst`, INDEPENDENT of `aslot`'s own sign
formula (the substitution carries the whole instance, sign included,
uniformly). -/
theorem gGbrCastFst_aslot (q r : G) {p p' : G} (h : p = p')
    (τ : (Γ.D p).carrier) (w : GBR Γ p q r) :
    gGbrCastFst K Γ q r h (τ • w) = (Γ.gaugeCast h).toAlgEquiv τ • gGbrCastFst K Γ q r h w := by
  subst h
  rfl

/-- **`gq5v7Close`, THE NEW DEVICE**: `F_{a,b+c} ⊗[D_{a+b+c}] GBR Γ
(a+b+c) d e ≃ GQ5 K Γ a (b+c) d e`, mirroring `gblOuterCastV2`'s
two-`RelTensor.lift`-leg construction VERBATIM: identity on the shared
first factor `F_{a,b+c}`, `gGbrCastFst` on the second — the "GBR-first-
argument index cast" one level up. Built via `RelTensor.lift` (NOT
`RelTensor.mapEquivRight`, since the two sides' `D_{a+b+c}`-actions on the
SECOND factor genuinely differ — `gGbrCastFst_aslot`'s intertwining is
TWISTED by `Γ.gaugeCast`, not the identity `RelTensor.mapEquivRight`
needs). -/
private noncomputable def gq5v7CloseFwdBilin :
    FusionColumn (Γ.fuse a (b + c)) →ₗ[K] GBR Γ (a + b + c) d e →ₗ[K] GQ5 K Γ a (b + c) d e :=
  (RelTensor.mk K (Γ.D (a + (b + c))).carrier (FusionColumn (Γ.fuse a (b + c)))
    (GBR Γ (a + (b + c)) d e)).compl₂ (gGbrCastFst K Γ d e (add_assoc a b c)).toLinearMap

private theorem gq5v7CloseFwdBilin_apply (v : FusionColumn (Γ.fuse a (b + c)))
    (w : GBR Γ (a + b + c) d e) :
    gq5v7CloseFwdBilin K Γ a b c d e v w
      = RelTensor.mk K (Γ.D (a + (b + c))).carrier (FusionColumn (Γ.fuse a (b + c)))
          (GBR Γ (a + (b + c)) d e) v (gGbrCastFst K Γ d e (add_assoc a b c) w) := rfl

private theorem gq5v7CloseFwd_balanced :
    RelTensor.IsBalanced (Γ.D (a + b + c)).carrier (gq5v7CloseFwdBilin K Γ a b c d e) := by
  intro t v w
  rw [gq5v7CloseFwdBilin_apply, gq5v7CloseFwdBilin_apply, gGbrCastFst_aslot,
    fusionColumn_recast_op_smul_def, RelTensor.mk_op_smul]

private noncomputable def gq5v7CloseFwd :
    RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
        (GBR Γ (a + b + c) d e) →ₗ[K]
      GQ5 K Γ a (b + c) d e :=
  RelTensor.lift (gq5v7CloseFwdBilin K Γ a b c d e) (gq5v7CloseFwd_balanced K Γ a b c d e)

private theorem gq5v7CloseFwd_mk (v : FusionColumn (Γ.fuse a (b + c))) (w : GBR Γ (a + b + c) d e) :
    gq5v7CloseFwd K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
          (GBR Γ (a + b + c) d e) v w)
      = RelTensor.mk K (Γ.D (a + (b + c))).carrier (FusionColumn (Γ.fuse a (b + c)))
          (GBR Γ (a + (b + c)) d e) v (gGbrCastFst K Γ d e (add_assoc a b c) w) := by
  show RelTensor.lift (gq5v7CloseFwdBilin K Γ a b c d e) (gq5v7CloseFwd_balanced K Γ a b c d e)
      (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
        (GBR Γ (a + b + c) d e) v w) = _
  rw [RelTensor.lift_mk, gq5v7CloseFwdBilin_apply]

private noncomputable def gq5v7CloseBwdBilin :
    FusionColumn (Γ.fuse a (b + c)) →ₗ[K] GBR Γ (a + (b + c)) d e →ₗ[K]
      RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
        (GBR Γ (a + b + c) d e) :=
  (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
    (GBR Γ (a + b + c) d e)).compl₂ (gGbrCastFst K Γ d e (add_assoc a b c)).symm.toLinearMap

private theorem gq5v7CloseBwdBilin_apply (v : FusionColumn (Γ.fuse a (b + c)))
    (w : GBR Γ (a + (b + c)) d e) :
    gq5v7CloseBwdBilin K Γ a b c d e v w
      = RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
          (GBR Γ (a + b + c) d e) v ((gGbrCastFst K Γ d e (add_assoc a b c)).symm w) := rfl

private theorem gq5v7CloseBwd_balanced :
    RelTensor.IsBalanced (Γ.D (a + (b + c))).carrier (gq5v7CloseBwdBilin K Γ a b c d e) := by
  intro s v w
  rw [gq5v7CloseBwdBilin_apply, gq5v7CloseBwdBilin_apply,
    show (gGbrCastFst K Γ d e (add_assoc a b c)).symm (s • w)
        = (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv.symm s •
            (gGbrCastFst K Γ d e (add_assoc a b c)).symm w from by
      have h := gGbrCastFst_aslot K Γ d e (add_assoc a b c)
        ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv.symm s)
        ((gGbrCastFst K Γ d e (add_assoc a b c)).symm w)
      rw [AlgEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
      rw [← h, LinearEquiv.symm_apply_apply],
    show (MulOpposite.op s • v : FusionColumn (Γ.fuse a (b + c)))
        = MulOpposite.op ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv.symm s) • v from by
      rw [fusionColumn_recast_op_smul_def, AlgEquiv.apply_symm_apply],
    RelTensor.mk_op_smul]

private noncomputable def gq5v7CloseBwd :
    GQ5 K Γ a (b + c) d e →ₗ[K]
      RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
        (GBR Γ (a + b + c) d e) :=
  RelTensor.lift (gq5v7CloseBwdBilin K Γ a b c d e) (gq5v7CloseBwd_balanced K Γ a b c d e)

private theorem gq5v7CloseBwd_mk (v : FusionColumn (Γ.fuse a (b + c))) (w : GBR Γ (a + (b + c)) d e) :
    gq5v7CloseBwd K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + (b + c))).carrier (FusionColumn (Γ.fuse a (b + c)))
          (GBR Γ (a + (b + c)) d e) v w)
      = RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
          (GBR Γ (a + b + c) d e) v ((gGbrCastFst K Γ d e (add_assoc a b c)).symm w) := by
  show RelTensor.lift (gq5v7CloseBwdBilin K Γ a b c d e) (gq5v7CloseBwd_balanced K Γ a b c d e)
      (RelTensor.mk K (Γ.D (a + (b + c))).carrier (FusionColumn (Γ.fuse a (b + c)))
        (GBR Γ (a + (b + c)) d e) v w) = _
  rw [RelTensor.lift_mk, gq5v7CloseBwdBilin_apply]

private theorem gq5v7CloseFwd_bwd :
    (gq5v7CloseFwd K Γ a b c d e).comp (gq5v7CloseBwd K Γ a b c d e) = LinearMap.id := by
  refine RelTensor.hom_ext fun v w => ?_
  show gq5v7CloseFwd K Γ a b c d e
      (gq5v7CloseBwd K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + (b + c))).carrier (FusionColumn (Γ.fuse a (b + c)))
          (GBR Γ (a + (b + c)) d e) v w))
    = RelTensor.mk K (Γ.D (a + (b + c))).carrier (FusionColumn (Γ.fuse a (b + c)))
        (GBR Γ (a + (b + c)) d e) v w
  rw [gq5v7CloseBwd_mk, gq5v7CloseFwd_mk, LinearEquiv.apply_symm_apply]

private theorem gq5v7CloseBwd_fwd :
    (gq5v7CloseBwd K Γ a b c d e).comp (gq5v7CloseFwd K Γ a b c d e) = LinearMap.id := by
  refine RelTensor.hom_ext fun v w => ?_
  show gq5v7CloseBwd K Γ a b c d e (gq5v7CloseFwd K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
        (GBR Γ (a + b + c) d e) v w))
    = RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
        (GBR Γ (a + b + c) d e) v w
  rw [gq5v7CloseFwd_mk, gq5v7CloseBwd_mk, LinearEquiv.symm_apply_apply]

noncomputable def gq5v7Close :
    RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e)
      ≃ₗ[K] GQ5 K Γ a (b + c) d e :=
  LinearEquiv.ofLinear (gq5v7CloseFwd K Γ a b c d e) (gq5v7CloseBwd K Γ a b c d e)
    (gq5v7CloseFwd_bwd K Γ a b c d e) (gq5v7CloseBwd_fwd K Γ a b c d e)

theorem gq5v7Close_mk (v : FusionColumn (Γ.fuse a (b + c))) (w : GBR Γ (a + b + c) d e) :
    gq5v7Close K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
          (GBR Γ (a + b + c) d e) v w)
      = RelTensor.mk K (Γ.D (a + (b + c))).carrier (FusionColumn (Γ.fuse a (b + c)))
          (GBR Γ (a + (b + c)) d e) v (gGbrCastFst K Γ d e (add_assoc a b c) w) :=
  gq5v7CloseFwd_mk K Γ a b c d e v w

/-- `gq5v7Close`'s `D_{b+c}`-slot equivariance, unconditional: the device
only ever touches the SECOND factor, so it commutes freely with
`F_{a,b+c}`'s own `(b+c)`-slot (`GQ5.bslot_smul_mk`) on the other side. -/
theorem gq5v7Close_bcSlot (y : (Γ.D (b + c)).carrier)
    (n : RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
      (GBR Γ (a + b + c) d e)) :
    gq5v7Close K Γ a b c d e (y • n) = y • gq5v7Close K Γ a b c d e n := by
  induction n using RelTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | mk v w =>
      have hL : gq5v7Close K Γ a b c d e
          (y • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
            (GBR Γ (a + b + c) d e) v w)
        = RelTensor.mk K (Γ.D (a + (b + c))).carrier (FusionColumn (Γ.fuse a (b + c)))
            (GBR Γ (a + (b + c)) d e) (y • v) (gGbrCastFst K Γ d e (add_assoc a b c) w) := by
        rw [show (y • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
              (GBR Γ (a + b + c) d e) v w
              : RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                  (GBR Γ (a + b + c) d e))
            = RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                (GBR Γ (a + b + c) d e) (y • v) w from
          leftActionEnd_mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
            (GBR Γ (a + b + c) d e) y v w,
          gq5v7Close_mk]
      have hR : y • gq5v7Close K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
            (GBR Γ (a + b + c) d e) v w)
        = RelTensor.mk K (Γ.D (a + (b + c))).carrier (FusionColumn (Γ.fuse a (b + c)))
            (GBR Γ (a + (b + c)) d e) (y • v) (gGbrCastFst K Γ d e (add_assoc a b c) w) := by
        rw [gq5v7Close_mk]
        exact leftActionEnd_mk K (Γ.D (a + (b + c))).carrier (FusionColumn (Γ.fuse a (b + c)))
          (GBR Γ (a + (b + c)) d e) y v (gGbrCastFst K Γ d e (add_assoc a b c) w)
      rw [hL, hR]
  | add x y' hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]

/-- **`omegaPbcV7`**: `omegaPbcV7Step1` then `gq5v7Close` wrapped under the
outer `F_{b,c}` spectator — landing the literal `GQ5 K Γ a (b+c) d e`. -/
noncomputable def omegaPbcV7 : V7 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ5 K Γ a (b + c) d e) :=
  (omegaPbcV7Step1 K Γ a b c d e).trans
    (RelTensor.mapEquivRight K (gq5v7Close K Γ a b c d e) (gq5v7Close_bcSlot K Γ a b c d e))

/-- **The sign-free generator formula of `omegaPbcV7`.** -/
theorem omegaPbcV7_mk (u : FusionColumn (Γ.fuse b c)) (v : FusionColumn (Γ.fuse a (b + c)))
    (w : GBR Γ (a + b + c) d e) :
    omegaPbcV7 K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c) (GBR Γ (a + b + c) d e)
          (GBR.mk Γ a b c u v) w)
      = RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ5 K Γ a (b + c) d e) u
          (GQ5.mk K Γ a (b + c) d e v (gGbrCastFst K Γ d e (add_assoc a b c) w)) := by
  have h1 := omegaPbcV7Step1_mk K Γ a b c d e u v w
  show RelTensor.mapEquivRight K (gq5v7Close K Γ a b c d e) (gq5v7Close_bcSlot K Γ a b c d e)
      (omegaPbcV7Step1 K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c) (GBR Γ (a + b + c) d e)
          (GBR.mk Γ a b c u v) w)) = _
  rw [h1]
  show RelTensor.map (LinearMap.id : FusionColumn (Γ.fuse b c) →ₗ[K] FusionColumn (Γ.fuse b c))
      (gq5v7Close K Γ a b c d e).toLinearMap (fun _ _ => rfl) (gq5v7Close_bcSlot K Γ a b c d e)
      (RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
        (RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
          (GBR Γ (a + b + c) d e)) u
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
          (GBR Γ (a + b + c) d e) v w)) = _
  rw [RelTensor.map_mk, LinearMap.id_apply]
  simp only [LinearEquiv.coe_toLinearMap]
  rw [gq5v7Close_mk]
  rfl

end OmegaPbcV7

/-! ### `omegaPbcV2_mk`: the missing leaf for `QuintExtract5.lean`'s
`omegaPbcV2` -/

section OmegaPbcV2Leaf

/-- **The sign-free generator formula of `omegaPbcV2`** (`QuintExtract5.lean`) —
mirrors `omegaPbcV10_mk`'s proof shape verbatim. -/
theorem omegaPbcV2_mk (u : FusionColumn (Γ.fuse b c)) (v : FusionColumn (Γ.fuse a (b + c)))
    (x : FusionColumn (Γ.fuse (a + b + c) d)) (t : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    omegaPbcV2 K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ2 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) x) t)
      = RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ1 K Γ a (b + c) d e) u
          (gblOuterCastV2 K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBL Γ a (b + c) d)
              (FusionColumn (Γ.fuse (a + b + c + d) e))
              (GBL.mk Γ a (b + c) d v (gColumnCastFst K Γ d (add_assoc a b c) x)) t)) := by
  have h1 : (PentagonB.RelTensor.mapEquivLeft K (gq2Assoc K Γ a b c d)
        (gq2Assoc_rightTotal K Γ a b c d))
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ2 K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e))
        (GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) x) t)
    = RelTensor.mk K (Γ.D (a + b + c + d)).carrier
        (RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ2rInner K Γ a b c d))
        (FusionColumn (Γ.fuse (a + b + c + d) e))
        (gq2Assoc K Γ a b c d (GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) x)) t :=
    RelTensor.map_mk (gq2Assoc K Γ a b c d).toLinearMap
      (LinearMap.id : FusionColumn (Γ.fuse (a + b + c + d) e) →ₗ[K]
        FusionColumn (Γ.fuse (a + b + c + d) e))
      (gq2Assoc_rightTotal K Γ a b c d) (fun _ _ => rfl)
      (GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) x) t
  have hgq2 : gq2Assoc K Γ a b c d (GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) x)
      = RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
          (RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
            (FusionColumn (Γ.fuse (a + b + c) d))) u
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
            (FusionColumn (Γ.fuse (a + b + c) d)) v x) :=
    gq2Assoc_mk K Γ a b c d u v x
  rw [hgq2] at h1
  have h2 := RelTensor.assoc_mk K (Γ.D (b + c)).carrier (Γ.D (a + b + c + d)).carrier
    (FusionColumn (Γ.fuse b c)) (GQ2rInner K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
    u (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
      (FusionColumn (Γ.fuse (a + b + c) d)) v x) t
  have h3 := gq2rCastMapLeftV2_mk K Γ a b c d e
    (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
      (FusionColumn (Γ.fuse (a + b + c) d)) v x) t
  rw [gq2rCast_mk] at h3
  have h4 := gblOuterCastV2_mk K Γ a b c d e
    (GBL.mk Γ a (b + c) d v (gColumnCastFst K Γ d (add_assoc a b c) x)) t
  show RelTensor.mapEquivRight K (gq2rCastWrappedV2 K Γ a b c d e)
      (gq2rCastWrappedV2_bcSlot K Γ a b c d e)
      (RelTensor.assoc K (Γ.D (b + c)).carrier (Γ.D (a + b + c + d)).carrier
        (FusionColumn (Γ.fuse b c)) (GQ2rInner K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e))
        ((PentagonB.RelTensor.mapEquivLeft K (gq2Assoc K Γ a b c d)
          (gq2Assoc_rightTotal K Γ a b c d))
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ2 K Γ a b c d)
            (FusionColumn (Γ.fuse (a + b + c + d) e))
            (GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) x) t))) = _
  rw [h1, h2]
  show RelTensor.map (LinearMap.id : FusionColumn (Γ.fuse b c) →ₗ[K] FusionColumn (Γ.fuse b c))
      (gq2rCastWrappedV2 K Γ a b c d e).toLinearMap (fun _ _ => rfl)
      (gq2rCastWrappedV2_bcSlot K Γ a b c d e)
      (RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
        (RelTensor K (Γ.D (a + b + c + d)).carrier (GQ2rInner K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e))) u
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ2rInner K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e))
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
            (FusionColumn (Γ.fuse (a + b + c) d)) v x) t)) = _
  rw [RelTensor.map_mk, LinearMap.id_apply]
  simp only [LinearEquiv.coe_toLinearMap]
  show RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ1 K Γ a (b + c) d e) u
      (gq2rCastWrappedV2 K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ2rInner K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e))
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
            (FusionColumn (Γ.fuse (a + b + c) d)) v x) t)) = _
  show RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ1 K Γ a (b + c) d e) u
      (gblOuterCastV2 K Γ a b c d e
        ((PentagonB.RelTensor.mapEquivLeft K (gq2rCast K Γ a b c d)
          (gq2rCast_totalSlot K Γ a b c d))
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ2rInner K Γ a b c d)
            (FusionColumn (Γ.fuse (a + b + c + d) e))
            (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
              (FusionColumn (Γ.fuse (a + b + c) d)) v x) t))) = _
  rw [h3, h4]

end OmegaPbcV2Leaf

/-! ### `E2M_leaf` -/

section E2MLeaf

/-- **`E2M_leaf`**: `E2M`'s (`QuintEdges2.lean`) generator formula on a
FULLY-DECOMPOSED `V2`-generator — `E2M` is a bare `RelTensor.map` of the
`GE2`-role map at the FIXED datum `gt2Canon (gTCanon Γ a (b+c) d)`, so this
is a direct two-step chase (`RelTensor.map_mk` then `GE2_mk_of_mem`), no
new toolkit content. -/
theorem E2M_leaf {ju : ZMod 2} {u : FusionColumn (Γ.fuse b c)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse b c) ju)
    (v : FusionColumn (Γ.fuse a (b + c))) (x : FusionColumn (Γ.fuse (a + b + c) d))
    (t : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    E2M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ2 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) x) t)
      = ((sgn (gParity K Γ a (b + c) d * ju) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ3 K Γ a b c d)
            (FusionColumn (Γ.fuse (a + b + c + d) e))
            (GQ3.mk K Γ a b c d u
              (gt2Canon K Γ a b c d (gTCanon K Γ a (b + c) d)
                (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                  (FusionColumn (Γ.fuse (a + b + c) d)) v x))) t := by
  have hge2 : GE2 K Γ a b c d (gParity K Γ a (b + c) d)
        (gt2Canon K Γ a b c d (gTCanon K Γ a (b + c) d)).toLinearMap
        (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
          (gTCanon_mem_gInterSpace K Γ a (b + c) d))
        (GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) x)
      = ((sgn (gParity K Γ a (b + c) d * ju) : ℤˣ) : ℤ) •
          GQ3.mk K Γ a b c d u
            (gt2Canon K Γ a b c d (gTCanon K Γ a (b + c) d)
              (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                (FusionColumn (Γ.fuse (a + b + c) d)) v x)) :=
    GE2_mk_of_mem K Γ a b c d (gParity K Γ a (b + c) d)
      (gt2Canon K Γ a b c d (gTCanon K Γ a (b + c) d)).toLinearMap
      (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
        (gTCanon_mem_gInterSpace K Γ a (b + c) d)) hu v x
  show RelTensor.map (GE2 K Γ a b c d (gParity K Γ a (b + c) d)
      (gt2Canon K Γ a b c d (gTCanon K Γ a (b + c) d)).toLinearMap
      (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
        (gTCanon_mem_gInterSpace K Γ a (b + c) d)))
      LinearMap.id (GE2_rightTotal K Γ a b c d) (fun _ _ => rfl)
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ2 K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e))
        (GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) x) t) = _
  simp only [RelTensor.map_mk, LinearMap.id_apply, hge2, map_zsmul, LinearMap.smul_apply]

end E2MLeaf

/-! ### `E16M_general` -/

section E16MGeneral

/-- **`E16M_general`**: the `GBR.grading Γ a b c`-only-keyed generalization
of `E16M`'s (`QuintEdges6.lean`) generator formula — `Z : F_{a+b+c,d}` and
`n : F_{a+b+c+d,e}` are BOTH left completely opaque (`gE16Step`'s own
`smap` layer is keyed only to `u`'s grading, per `smap_mk_of_mem`'s
hypothesis shape). "Nearly free" per the referees: `gV2Assoc` then
`gE16Step`'s own `smapEquiv`/`smap_mk_of_mem`. -/
theorem E16M_general {ju : ZMod 2} {u : GBR Γ a b c} (hu : u ∈ GBR.grading Γ a b c ju)
    (Z : FusionColumn (Γ.fuse (a + b + c) d)) (n : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    E16M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ2 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) (GQ2.mk K Γ a b c d u Z) n)
      = ((sgn (gParity K Γ (a + b + c) d e * ju) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c) (GBR Γ (a + b + c) d e) u
            (gTCanon K Γ (a + b + c) d e
              (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (FusionColumn (Γ.fuse (a + b + c) d))
                (FusionColumn (Γ.fuse (a + b + c + d) e)) Z n)) := by
  have h1 : gV2Assoc K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ2 K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) (GQ2.mk K Γ a b c d u Z) n)
    = RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c) (GBL Γ (a + b + c) d e) u
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (FusionColumn (Γ.fuse (a + b + c) d))
          (FusionColumn (Γ.fuse (a + b + c + d) e)) Z n) :=
    RelTensor.assoc_mk K (Γ.D (a + b + c)).carrier (Γ.D (a + b + c + d)).carrier
      (GBR Γ a b c) (FusionColumn (Γ.fuse (a + b + c) d)) (FusionColumn (Γ.fuse (a + b + c + d) e))
      u Z n
  show gE16Step K Γ a b c d e
      (gV2Assoc K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ2 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) (GQ2.mk K Γ a b c d u Z) n)) = _
  rw [h1]
  show smap (Γ.D (a + b + c)).grading (GBR.grading Γ a b c)
      (gTCanon K Γ (a + b + c) d e).toLinearMap (gParity K Γ (a + b + c) d e)
      (gCanonHphi4 K Γ (a + b) c d e)
      (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c) (GBL Γ (a + b + c) d e) u
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (FusionColumn (Γ.fuse (a + b + c) d))
          (FusionColumn (Γ.fuse (a + b + c + d) e)) Z n)) = _
  simp only [smap_mk_of_mem (Γ.D (a + b + c)).grading (GBR.grading Γ a b c)
    (gTCanon K Γ (a + b + c) d e).toLinearMap (gParity K Γ (a + b + c) d e)
    (gCanonHphi4 K Γ (a + b) c d e) hu, LinearEquiv.coe_toLinearMap]

end E16MGeneral

/-! ### `E9M_leaf` -/

section E9MLeaf

/-- **`E9M_leaf`**: `E9M`'s (`QuintEdges.lean`) generator formula on a
FULLY-DECOMPOSED `V10`-generator — `E9M` is a bare `RelTensor.map` of the
`GE4`-role map at the SHIFTED quadruple `(b,c,d,e)`, the `E4M`/`E20M`-genre
two-step chase (`RelTensor.map_mk` then `GE4_mk_of_mem`). -/
theorem E9M_leaf {ju : ZMod 2} {u : FusionColumn (Γ.fuse b c)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse b c) ju) (v : FusionColumn (Γ.fuse (b + c) d))
    (w : FusionColumn (Γ.fuse (b + c + d) e)) (t : FusionColumn (Γ.fuse a (b + c + d + e))) :
    E9M K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ1 K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e)))
          (GQ1.mk K Γ b c d e (GBL.mk Γ b c d u v) w) t)
      = ((sgn (gParity K Γ (b + c) d e * ju) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ5 K Γ b c d e)
            (FusionColumn (Γ.fuse a (b + c + d + e)))
            (GQ5.mk K Γ b c d e u
              (gTCanon K Γ (b + c) d e (GBL.mk Γ (b + c) d e v w))) t := by
  have hge4 : GE4 K Γ b c d e (gParity K Γ (b + c) d e)
        (gTCanon K Γ (b + c) d e).toLinearMap (gCanonHphi4 K Γ b c d e)
        (GQ1.mk K Γ b c d e (GBL.mk Γ b c d u v) w)
      = ((sgn (gParity K Γ (b + c) d e * ju) : ℤˣ) : ℤ) •
          GQ5.mk K Γ b c d e u (gTCanon K Γ (b + c) d e (GBL.mk Γ (b + c) d e v w)) :=
    GE4_mk_of_mem K Γ b c d e (gParity K Γ (b + c) d e) (gTCanon K Γ (b + c) d e).toLinearMap
      (gCanonHphi4 K Γ b c d e) hu v w
  show RelTensor.map (GE4 K Γ b c d e (gParity K Γ (b + c) d e)
      (gTCanon K Γ (b + c) d e).toLinearMap (gCanonHphi4 K Γ b c d e))
      LinearMap.id (GE4_rightTotal K Γ b c d e) (fun _ _ => rfl)
      (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ1 K Γ b c d e)
        (FusionColumn (Γ.fuse a (b + c + d + e)))
        (GQ1.mk K Γ b c d e (GBL.mk Γ b c d u v) w) t) = _
  simp only [RelTensor.map_mk, LinearMap.id_apply, hge4, map_zsmul, LinearMap.smul_apply]

end E9MLeaf

end GaugeChi

end Superfusion
