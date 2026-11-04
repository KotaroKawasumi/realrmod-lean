/-
Superfusion / GaugeChi / QuintEdges3

Milestone M13-2″ of the abstract `(p, χ)` arc: **the four-letter recast
device** and the two "cluster-tier" edges it was built for, `E13M` (`V1 →
V6`, the move `t_{a+b+c,d,e}`) and `E15M` (`V4 → V10`, the move
`t_{a,b+c+d,e}`), continuing `GaugeChi.QuintEdges2`.

**Derivation record (the two edges' ACTUAL requirements, worked out from
the ledger, not merely mirrored a priori):**

`V1 = (((ab)c)d)e = GQ1(a,b,c,d) ⊗_{D_{a+b+c+d}} F_{a+b+c+d,e}` unfolds
(both `GQ1` and `V1` being `def`s) to the literal iterated tensor
`(GBL(a,b,c) ⊗_{D_{a+b+c}} F_{a+b+c,d}) ⊗_{D_{a+b+c+d}} F_{a+b+c+d,e}`.
Since `a+b+c` is a *prefix* cluster, `(a+b+c)+d` is syntactically the
SAME term as `a+b+c+d` (both parse to `((a+b)+c)+d`), so a single
`RelTensor.assoc` already lands EXACTLY on `GBL(a,b,c) ⊗_{D_{a+b+c}}
GBL(a+b+c,d,e)` — no cast of any kind is needed for `E13M`'s own
construction (`gV1Assoc`); the whiskering step is then the signed
`(a+b+c)`-slot amplification of `gTCanon Γ (a+b+c) d e` (`smap`, using
the ALREADY-PUBLIC `gCanonHphi4 K Γ (a+b) c d e` — `(a+b)+c = a+b+c`
syntactically, so this is a literal reuse, not a new fact).

`V4 = (a((bc)d))e = GQ3(a,b,c,d) ⊗_{D_{a+b+c+d}} F_{a+b+c+d,e}` and `V10
= a(((bc)d)e) = GQ1(b,c,d,e) ⊗_{D_{b+c+d+e}} F_{a,b+c+d+e}` are related
at the *middle* cluster `(b+c+d)`: `a + (b+c+d)` (right-nested at the
cluster) is a DIFFERENT term from `a+b+c+d` (left-nested) — this is
where the recast genuinely bites. `gq3Assoc.symm` (Pentagon.lean,
ALREADY built, with `Total`-naturality already public via
`gq3Assoc_rightTotal_general`, `QuintEdges.lean`) peels `V4` down to
`GBL(b,c,d) ⊗_{D_{b+c+d}} F_{a,b+c+d}` inside its own `D_{a+b+c+d}`-outer
tensor; ONE further `RelTensor.assoc` (using `Quint.lean`'s
ALREADY-LANDED `FourLetterRecast` instances on `F_{a,b+c+d}`, at
`w,x,y,z := a,b,c,d`) exposes the innermost `F_{a,b+c+d}
⊗_{D_{a+b+c+d}}(recast) F_{a+b+c+d,e}` — which is *exactly* `gq2rCast`'s
own shape, mirrored one level up (**`gFourCast`**, deliverable 1 below):
identity on the shared first factor `F_{a,b+c+d}`, `gColumnCastFst`
(reused verbatim, `ChiCanon.lean`) on the second, using
`add_assoc_four`/`fusionColumnRecast4_op_smul_def` (`Quint.lean`) in
place of `add_assoc`/`fusionColumn_recast_op_smul_def`. The device
recasts `F_{a,b+c+d} ⊗_{D_{a+b+c+d}} F_{a+b+c+d,e}` (the RECAST
coefficient, `Quint.lean`'s `instModuleFusionColumnRecast4`) to
`GBL(a,b+c+d,e)` (natural). The whiskering is then the SIGNED
`(b+c+d)`-slot (middle-slot) amplification of `gTCanon Γ a (b+c+d) e`
(`smap`, via **`gCanonMidSlot`**, the public restatement of
`gInterSpace`'s `.2.2.1` conjunct — the middle-slot analogue of
`ChiCanon.lean`'s already-public `gCanonHphi4`/`gCanonHphi5`, sourced
from the SAME `mem_gInterSpace_iff`). `V10`'s own side needs only a
single UNCAST `RelTensor.assoc` (`gV10Assoc`, `(b+c+d)+e = b+c+d+e`
syntactically, mirroring `V1`'s own prefix-cluster simplicity).

**Deviation from the round's a priori scoping note**
(`QuintEdges.lean`'s closing remarks): that note anticipated `E13M`
ALSO needing a four-letter recast and "TWO assoc layers each" for BOTH
edges; the precise derivation above shows `E13M` needs NEITHER (a
single, cast-free `RelTensor.assoc` + `smap`) — the recast device is
consumed by `E15M` alone. Both edges are landed as genuine
`LinearEquiv`s (`E13Mequiv`/`E15Mequiv`), giving `E_kM`/`E_kM_bijective`
by simple projection, mirroring the `ChiCanon.lean`-style assembly
(`.toLinearMap`/`.bijective`) rather than a manual `Function.Bijective`
composite.

**New small toolkit pieces landed alongside the device** (both mirror
`ChiAbs.lean`'s `PentagonB` layer-2 devices one slot over, since only the
LEFT/`M`-slot `LinearEquiv`-ization (`RelTensor.mapEquivLeft`) was
previously public):

* `leftEquivariant_symm`: the LEFT/`N`-slot companion of
  `PentagonB.rightEquivariant_symm` (if `φ` is left-`A`-equivariant, so
  is `φ.symm`).
* `RelTensor.mapEquivRight`: the RIGHT/`N`-slot companion of
  `PentagonB.RelTensor.mapEquivLeft` — `RelTensor.map id φ` is a
  `LinearEquiv` for an invertible left-equivariant `φ`.
* `gq3Assoc_symm_rightTotal`: `gq3Assoc.symm`'s `Total`-recast-naturality,
  a one-line corollary of the already-public `gq3Assoc_rightTotal_general`
  plus `gq3Assoc`'s own bijectivity (injectivity suffices).
-/
import Superfusion.GaugeChi.QuintEdges2

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)

attribute [local instance 500] leftModule rightModule

/-! ### Toolkit piece 16: the RIGHT/`N`-slot `LinearEquiv`-ization of
`RelTensor.map` (the mirror of `ChiAbs.lean`'s `PentagonB.RelTensor.
mapEquivLeft`, one slot over) -/

section MapEquivRight

variable {A : Type*} [Ring A]
variable {M : Type*} [AddCommGroup M] [Module K M] [Module Aᵐᵒᵖ M]
variable {N N' : Type*} [AddCommGroup N] [Module K N] [Module A N]
variable [AddCommGroup N'] [Module K N'] [Module A N']

omit [Invertible (2 : K)] in
/-- **The left-equivariant inverse** (the mirror of `ChiAbs.lean`'s
`rightEquivariant_symm`, for the LEFT/`MulOpposite`-free action shape
`RelTensor.map`'s SECOND-slot hypothesis takes): if `φ : N ≃ₗ[K] N'` is
left-`A`-equivariant, so is `φ.symm`. -/
theorem leftEquivariant_symm (φ : N ≃ₗ[K] N')
    (hφ : ∀ (a : A) (n : N), φ (a • n) = a • φ n) :
    ∀ (a : A) (n' : N'), φ.symm (a • n') = a • φ.symm n' := by
  intro a n'
  have h := hφ a (φ.symm n')
  rw [φ.apply_symm_apply] at h
  have h2 : φ.symm (φ (a • φ.symm n')) = φ.symm (a • n') := congrArg φ.symm h
  rw [φ.symm_apply_apply] at h2
  exact h2.symm

/-- **`RelTensor.map`'s right slot, `LinearEquiv`-ized**: for an
invertible left-equivariant generator `φ : N ≃ₗ[K] N'`, `RelTensor.map id
φ.toLinearMap _ hφ` is a `LinearEquiv` — the mirror of `ChiAbs.lean`'s
`PentagonB.RelTensor.mapEquivLeft`. -/
noncomputable def RelTensor.mapEquivRight (φ : N ≃ₗ[K] N')
    (hφ : ∀ (a : A) (n : N), φ (a • n) = a • φ n) :
    (M ⊗[A;K] N) ≃ₗ[K] (M ⊗[A;K] N') :=
  LinearEquiv.ofLinear
    (RelTensor.map (LinearMap.id : M →ₗ[K] M) φ.toLinearMap (fun _ _ => rfl) hφ)
    (RelTensor.map (LinearMap.id : M →ₗ[K] M) φ.symm.toLinearMap (fun _ _ => rfl)
      (leftEquivariant_symm K φ hφ))
    (RelTensor.hom_ext fun m n' => by simp [RelTensor.map_mk])
    (RelTensor.hom_ext fun m n => by simp [RelTensor.map_mk])

end MapEquivRight

/-! ### Toolkit piece 17 (deliverable 1): `gFourCast`, the four-letter
recast device — `gq2rCast` (`ChiCanon.lean`) mirrored one level up, at
`add_assoc_four` (`Quint.lean`) in place of `add_assoc`. Recasts
`F_{w,x+y+z} ⊗_{D_{w+x+y+z}}(recast) F_{w+x+y+z,v}` to `GBL Γ w (x+y+z)
v` (natural). Built exactly as `gq2rCast`: two `RelTensor.lift` legs
glued by `LinearEquiv.ofLinear`, identity on the shared first factor
`F_{w,x+y+z}`, `gColumnCastFst` (`ChiCanon.lean`, reused verbatim — it is
already generic in its equality hypothesis) on the second. -/

section FourLetterRecastDevice

variable (w x y z v : G)

private noncomputable def gFourCastFwdBilin :
    FusionColumn (Γ.fuse w (x + y + z)) →ₗ[K]
      FusionColumn (Γ.fuse (w + x + y + z) v) →ₗ[K] GBL Γ w (x + y + z) v :=
  (GBL.mk Γ w (x + y + z) v).compl₂ (gColumnCastFst K Γ v (add_assoc_four w x y z)).toLinearMap

private theorem gFourCastFwdBilin_apply (u : FusionColumn (Γ.fuse w (x + y + z)))
    (t : FusionColumn (Γ.fuse (w + x + y + z) v)) :
    gFourCastFwdBilin K Γ w x y z v u t
      = GBL.mk Γ w (x + y + z) v u (gColumnCastFst K Γ v (add_assoc_four w x y z) t) := rfl

private theorem gFourCastGBLMkEq (u : FusionColumn (Γ.fuse w (x + y + z)))
    (t : FusionColumn (Γ.fuse (w + (x + y + z)) v)) :
    GBL.mk Γ w (x + y + z) v u t
      = RelTensor.mk K (Γ.D (w + (x + y + z))).carrier
          (FusionColumn (Γ.fuse w (x + y + z))) (FusionColumn (Γ.fuse (w + (x + y + z)) v)) u t := rfl

private theorem gFourCastFwd_balanced :
    RelTensor.IsBalanced (Γ.D (w + x + y + z)).carrier (gFourCastFwdBilin K Γ w x y z v) := by
  intro t u s
  rw [gFourCastFwdBilin_apply, gFourCastFwdBilin_apply, gColumnCastFst_xslot, gFourCastGBLMkEq,
    gFourCastGBLMkEq, fusionColumnRecast4_op_smul_def, RelTensor.mk_op_smul]

private noncomputable def gFourCastFwd :
    RelTensor K (Γ.D (w + x + y + z)).carrier (FusionColumn (Γ.fuse w (x + y + z)))
        (FusionColumn (Γ.fuse (w + x + y + z) v)) →ₗ[K]
      GBL Γ w (x + y + z) v :=
  RelTensor.lift (gFourCastFwdBilin K Γ w x y z v) (gFourCastFwd_balanced K Γ w x y z v)

private theorem gFourCastFwd_mk (u : FusionColumn (Γ.fuse w (x + y + z)))
    (t : FusionColumn (Γ.fuse (w + x + y + z) v)) :
    gFourCastFwd K Γ w x y z v (RelTensor.mk K (Γ.D (w + x + y + z)).carrier
        (FusionColumn (Γ.fuse w (x + y + z))) (FusionColumn (Γ.fuse (w + x + y + z) v)) u t)
      = GBL.mk Γ w (x + y + z) v u (gColumnCastFst K Γ v (add_assoc_four w x y z) t) := by
  show RelTensor.lift (gFourCastFwdBilin K Γ w x y z v) (gFourCastFwd_balanced K Γ w x y z v)
      (RelTensor.mk K (Γ.D (w + x + y + z)).carrier
        (FusionColumn (Γ.fuse w (x + y + z))) (FusionColumn (Γ.fuse (w + x + y + z) v)) u t) = _
  rw [RelTensor.lift_mk, gFourCastFwdBilin_apply]

private noncomputable def gFourCastBwdBilin :
    FusionColumn (Γ.fuse w (x + y + z)) →ₗ[K]
      FusionColumn (Γ.fuse (w + (x + y + z)) v) →ₗ[K]
        RelTensor K (Γ.D (w + x + y + z)).carrier (FusionColumn (Γ.fuse w (x + y + z)))
          (FusionColumn (Γ.fuse (w + x + y + z) v)) :=
  (RelTensor.mk K (Γ.D (w + x + y + z)).carrier
      (FusionColumn (Γ.fuse w (x + y + z))) (FusionColumn (Γ.fuse (w + x + y + z) v))).compl₂
    (gColumnCastFst K Γ v (add_assoc_four w x y z)).symm.toLinearMap

private theorem gFourCastBwdBilin_apply (u : FusionColumn (Γ.fuse w (x + y + z)))
    (t : FusionColumn (Γ.fuse (w + (x + y + z)) v)) :
    gFourCastBwdBilin K Γ w x y z v u t
      = RelTensor.mk K (Γ.D (w + x + y + z)).carrier
          (FusionColumn (Γ.fuse w (x + y + z))) (FusionColumn (Γ.fuse (w + x + y + z) v)) u
          ((gColumnCastFst K Γ v (add_assoc_four w x y z)).symm t) := rfl

private theorem gFourCastBwd_balanced :
    RelTensor.IsBalanced (Γ.D (w + (x + y + z))).carrier (gFourCastBwdBilin K Γ w x y z v) := by
  intro s u t
  rw [gFourCastBwdBilin_apply, gFourCastBwdBilin_apply, gColumnCastFst_symm_xslot,
    show (MulOpposite.op s • u : FusionColumn (Γ.fuse w (x + y + z)))
        = MulOpposite.op ((Γ.gaugeCast (add_assoc_four w x y z)).toAlgEquiv.symm s) • u from by
      rw [fusionColumnRecast4_op_smul_def, AlgEquiv.apply_symm_apply],
    RelTensor.mk_op_smul]

private noncomputable def gFourCastBwd :
    GBL Γ w (x + y + z) v →ₗ[K]
      RelTensor K (Γ.D (w + x + y + z)).carrier (FusionColumn (Γ.fuse w (x + y + z)))
        (FusionColumn (Γ.fuse (w + x + y + z) v)) :=
  RelTensor.lift (gFourCastBwdBilin K Γ w x y z v) (gFourCastBwd_balanced K Γ w x y z v)

private theorem gFourCastBwd_mk (u : FusionColumn (Γ.fuse w (x + y + z)))
    (t : FusionColumn (Γ.fuse (w + (x + y + z)) v)) :
    gFourCastBwd K Γ w x y z v (GBL.mk Γ w (x + y + z) v u t)
      = RelTensor.mk K (Γ.D (w + x + y + z)).carrier
          (FusionColumn (Γ.fuse w (x + y + z))) (FusionColumn (Γ.fuse (w + x + y + z) v)) u
          ((gColumnCastFst K Γ v (add_assoc_four w x y z)).symm t) := by
  show RelTensor.lift (gFourCastBwdBilin K Γ w x y z v) (gFourCastBwd_balanced K Γ w x y z v)
      (RelTensor.mk K (Γ.D (w + (x + y + z))).carrier
        (FusionColumn (Γ.fuse w (x + y + z))) (FusionColumn (Γ.fuse (w + (x + y + z)) v)) u t) = _
  rw [RelTensor.lift_mk, gFourCastBwdBilin_apply]

private theorem gFourCastFwd_bwd :
    (gFourCastFwd K Γ w x y z v).comp (gFourCastBwd K Γ w x y z v) = LinearMap.id := by
  refine RelTensor.hom_ext fun u t => ?_
  show gFourCastFwd K Γ w x y z v (gFourCastBwd K Γ w x y z v (GBL.mk Γ w (x + y + z) v u t))
    = GBL.mk Γ w (x + y + z) v u t
  rw [gFourCastBwd_mk, gFourCastFwd_mk, LinearEquiv.apply_symm_apply]

private theorem gFourCastBwd_fwd :
    (gFourCastBwd K Γ w x y z v).comp (gFourCastFwd K Γ w x y z v) = LinearMap.id := by
  refine RelTensor.hom_ext fun u t => ?_
  show gFourCastBwd K Γ w x y z v (gFourCastFwd K Γ w x y z v
      (RelTensor.mk K (Γ.D (w + x + y + z)).carrier
        (FusionColumn (Γ.fuse w (x + y + z))) (FusionColumn (Γ.fuse (w + x + y + z) v)) u t))
    = RelTensor.mk K (Γ.D (w + x + y + z)).carrier
        (FusionColumn (Γ.fuse w (x + y + z))) (FusionColumn (Γ.fuse (w + x + y + z) v)) u t
  rw [gFourCastFwd_mk, gFourCastBwd_mk, LinearEquiv.symm_apply_apply]

/-- **`gFourCast`**: the four-letter recast device (deliverable 1),
`gq2rCast` mirrored one level up. -/
noncomputable def gFourCast :
    RelTensor K (Γ.D (w + x + y + z)).carrier (FusionColumn (Γ.fuse w (x + y + z)))
        (FusionColumn (Γ.fuse (w + x + y + z) v)) ≃ₗ[K]
      GBL Γ w (x + y + z) v :=
  LinearEquiv.ofLinear (gFourCastFwd K Γ w x y z v) (gFourCastBwd K Γ w x y z v)
    (gFourCastFwd_bwd K Γ w x y z v) (gFourCastBwd_fwd K Γ w x y z v)

theorem gFourCast_mk (u : FusionColumn (Γ.fuse w (x + y + z)))
    (t : FusionColumn (Γ.fuse (w + x + y + z) v)) :
    gFourCast K Γ w x y z v (RelTensor.mk K (Γ.D (w + x + y + z)).carrier
        (FusionColumn (Γ.fuse w (x + y + z))) (FusionColumn (Γ.fuse (w + x + y + z) v)) u t)
      = GBL.mk Γ w (x + y + z) v u (gColumnCastFst K Γ v (add_assoc_four w x y z) t) :=
  gFourCastFwd_mk K Γ w x y z v u t

/-- **`gFourCast`'s `(x+y+z)`-slot commutation, unconditionally** (the
four-letter mirror of `gq2rCast_bcSlot`): the action only ever touches
the untouched first factor `F_{w,x+y+z}`. -/
theorem gFourCast_midSlot (τ : (Γ.D (x + y + z)).carrier)
    (n : RelTensor K (Γ.D (w + x + y + z)).carrier (FusionColumn (Γ.fuse w (x + y + z)))
      (FusionColumn (Γ.fuse (w + x + y + z) v))) :
    gFourCast K Γ w x y z v (τ • n) = τ • gFourCast K Γ w x y z v n := by
  induction n using RelTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | mk u t =>
      have hR : τ • gFourCast K Γ w x y z v (RelTensor.mk K (Γ.D (w + x + y + z)).carrier
          (FusionColumn (Γ.fuse w (x + y + z))) (FusionColumn (Γ.fuse (w + x + y + z) v)) u t)
        = GBL.mk Γ w (x + y + z) v (τ • u) (gColumnCastFst K Γ v (add_assoc_four w x y z) t) := by
        rw [gFourCast_mk, GBL.bslot_smul_mk]
      have hL : gFourCast K Γ w x y z v (τ • RelTensor.mk K (Γ.D (w + x + y + z)).carrier
          (FusionColumn (Γ.fuse w (x + y + z))) (FusionColumn (Γ.fuse (w + x + y + z) v)) u t)
        = GBL.mk Γ w (x + y + z) v (τ • u) (gColumnCastFst K Γ v (add_assoc_four w x y z) t) := by
        rw [show (τ • RelTensor.mk K (Γ.D (w + x + y + z)).carrier
              (FusionColumn (Γ.fuse w (x + y + z))) (FusionColumn (Γ.fuse (w + x + y + z) v)) u t
              : RelTensor K (Γ.D (w + x + y + z)).carrier (FusionColumn (Γ.fuse w (x + y + z)))
                  (FusionColumn (Γ.fuse (w + x + y + z) v)))
            = RelTensor.mk K (Γ.D (w + x + y + z)).carrier (FusionColumn (Γ.fuse w (x + y + z)))
                (FusionColumn (Γ.fuse (w + x + y + z) v)) (τ • u) t from
          leftActionEnd_mk K (Γ.D (w + x + y + z)).carrier (FusionColumn (Γ.fuse w (x + y + z)))
            (FusionColumn (Γ.fuse (w + x + y + z) v)) τ u t,
          gFourCast_mk]
      rw [hL, hR]
  | add p q hp hq => rw [smul_add, map_add, map_add, smul_add, hp, hq]

end FourLetterRecastDevice

variable (a b c d e : G)

/-! ### Toolkit piece 18: `gCanonMidSlot`, the public restatement of
`gInterSpace`'s middle-slot (`.2.2.1`) conjunct — the middle-slot
analogue of `ChiCanon.lean`'s already-public `gCanonHphi4`/`gCanonHphi5`
(the FIRST- and THIRD-slot conjuncts), sourced from the SAME
`mem_gInterSpace_iff`, needed for `E15M`'s whiskering at the `(b+c+d)`
(middle) slot of `gTCanon Γ a (b+c+d) e`. -/

theorem gCanonMidSlot (x y z : G) :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D y).carrier⦄,
      τ ∈ (Γ.D y).grading i → ∀ n : GBL Γ x y z,
        gTCanon K Γ x y z (τ • n)
          = ((sgn (gParity K Γ x y z * i) : ℤˣ) : ℤ) • (τ • gTCanon K Γ x y z n) :=
  (mem_superEquivariant (Γ.D y).grading).mp
    ((mem_gInterSpace_iff K Γ x y z).mp (gTCanon_mem_gInterSpace K Γ x y z)).2.2.1

/-! ### Toolkit piece 19: `gq3Assoc.symm`'s `Total`-recast-naturality -/

/-- **`gq3Assoc.symm`'s `Total`-naturality**: a one-line corollary of the
already-public `gq3Assoc_rightTotal_general` (`QuintEdges.lean`) plus
`gq3Assoc`'s own injectivity — needed to whisker `gq3Assoc.symm` into
`V4`'s own outer `D_{a+b+c+d}`-slot via `RelTensor.mapEquivLeft`. -/
theorem gq3Assoc_symm_rightTotal (p q r s : G) (τ : (Γ.D (p + q + r + s)).carrier)
    (n : GQ3 K Γ p q r s) :
    (gq3Assoc K Γ p q r s).symm (MulOpposite.op τ • n)
      = MulOpposite.op τ • (gq3Assoc K Γ p q r s).symm n := by
  refine (gq3Assoc K Γ p q r s).injective ?_
  show gq3Assoc K Γ p q r s ((gq3Assoc K Γ p q r s).symm (MulOpposite.op τ • n))
    = gq3Assoc K Γ p q r s (rightActionEnd K (Γ.D (q + r + s)).carrier (GBL Γ q r s)
        (FusionColumn (Γ.fuse p (q + r + s))) (MulOpposite.op τ)
        ((gq3Assoc K Γ p q r s).symm n))
  rw [(gq3Assoc K Γ p q r s).apply_symm_apply, gq3Assoc_rightTotal_general,
    (gq3Assoc K Γ p q r s).apply_symm_apply]

/-! ### Edge 13: `E13M : V1 → V6`, `t_{a+b+c,d,e}` (owning faces `PAB`,
`S1`) -/

/-- **`gV1Assoc`**: `V1`'s own re-association, exposing `GBL(a+b+c,d,e)`
directly — a SINGLE, cast-free `RelTensor.assoc` (see the file docstring:
`a+b+c` is a prefix cluster, so no recast is needed). -/
noncomputable def gV1Assoc : V1 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (a + b + c)).carrier (GBL Γ a b c) (GBL Γ (a + b + c) d e) :=
  RelTensor.assoc K (Γ.D (a + b + c)).carrier (Γ.D (a + b + c + d)).carrier
    (GBL Γ a b c) (FusionColumn (Γ.fuse (a + b + c) d)) (FusionColumn (Γ.fuse (a + b + c + d) e))

/-- The signed `(a+b+c)`-slot whiskering of `gTCanon Γ (a+b+c) d e`,
landing `V6`'s own `GBR(a+b+c,d,e)` factor. -/
noncomputable def gE13Step :
    RelTensor K (Γ.D (a + b + c)).carrier (GBL Γ a b c) (GBL Γ (a + b + c) d e) ≃ₗ[K]
      RelTensor K (Γ.D (a + b + c)).carrier (GBL Γ a b c) (GBR Γ (a + b + c) d e) :=
  PentagonB.smapEquiv K (Γ.D (a + b + c)).grading (GBL.grading Γ a b c)
    (gTCanon K Γ (a + b + c) d e) (gParity K Γ (a + b + c) d e) (gCanonHphi4 K Γ (a + b) c d e)

/-- **`E13M`, as a `LinearEquiv`**: `gV1Assoc` then the signed
`(a+b+c)`-slot amplification. -/
noncomputable def E13Mequiv : V1 K Γ a b c d e ≃ₗ[K] V6 K Γ a b c d e :=
  (gV1Assoc K Γ a b c d e).trans (gE13Step K Γ a b c d e)

/-- **Edge 13** `E13M : V1 → V6`, `t_{a+b+c,d,e}` (owning faces `PAB`,
`S1`; presentation: `S1`, `gV1Assoc` then the whiskered `gTCanon Γ
(a+b+c) d e`). -/
noncomputable def E13M : V1 K Γ a b c d e →ₗ[K] V6 K Γ a b c d e :=
  (E13Mequiv K Γ a b c d e).toLinearMap

theorem E13M_bijective : Function.Bijective (E13M K Γ a b c d e) :=
  (E13Mequiv K Γ a b c d e).bijective

/-! ### Edge 15: `E15M : V4 → V10`, `t_{a,b+c+d,e}` (owning faces `PBC`,
`S2`) -/

/-- **`gV10Assoc`**: `V10`'s own re-association, exposing `GBR(a,b+c+d,e)`
directly — a SINGLE, cast-free `RelTensor.assoc` (`(b+c+d)+e = b+c+d+e`
syntactically, mirroring `V1`'s own prefix-cluster simplicity). -/
noncomputable def gV10Assoc : V10 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (b + c + d)).carrier (GBL Γ b c d) (GBR Γ a (b + c + d) e) :=
  RelTensor.assoc K (Γ.D (b + c + d)).carrier (Γ.D (b + c + d + e)).carrier
    (GBL Γ b c d) (FusionColumn (Γ.fuse (b + c + d) e)) (FusionColumn (Γ.fuse a (b + c + d + e)))

/-- Stage A of `gV4Assoc`: `gq3Assoc.symm` whiskered into `V4`'s own outer
`D_{a+b+c+d}`-slot, peeling `GQ3(a,b,c,d)` down to `GBL(b,c,d) ⊗_{D_{b+c+d}}
F_{a,b+c+d}`. -/
noncomputable def gV4AssocA : V4 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (a + b + c + d)).carrier
      (RelTensor K (Γ.D (b + c + d)).carrier (GBL Γ b c d) (FusionColumn (Γ.fuse a (b + c + d))))
      (FusionColumn (Γ.fuse (a + b + c + d) e)) :=
  PentagonB.RelTensor.mapEquivLeft K (gq3Assoc K Γ a b c d).symm
    (gq3Assoc_symm_rightTotal K Γ a b c d)

/-- Stage B of `gV4Assoc`: the associator exposing the innermost
`F_{a,b+c+d} ⊗_{D_{a+b+c+d}}(recast) F_{a+b+c+d,e}`, via `Quint.lean`'s
already-landed `FourLetterRecast` instances (`w,x,y,z := a,b,c,d`). -/
noncomputable def gV4AssocB :
    RelTensor K (Γ.D (a + b + c + d)).carrier
        (RelTensor K (Γ.D (b + c + d)).carrier (GBL Γ b c d) (FusionColumn (Γ.fuse a (b + c + d))))
        (FusionColumn (Γ.fuse (a + b + c + d) e)) ≃ₗ[K]
      RelTensor K (Γ.D (b + c + d)).carrier (GBL Γ b c d)
        (RelTensor K (Γ.D (a + b + c + d)).carrier (FusionColumn (Γ.fuse a (b + c + d)))
          (FusionColumn (Γ.fuse (a + b + c + d) e))) :=
  RelTensor.assoc K (Γ.D (b + c + d)).carrier (Γ.D (a + b + c + d)).carrier
    (GBL Γ b c d) (FusionColumn (Γ.fuse a (b + c + d))) (FusionColumn (Γ.fuse (a + b + c + d) e))

/-- Stage C of `gV4Assoc`: `gFourCast` (`w,x,y,z,v := a,b,c,d,e`) closing
the innermost recast pair into `GBL(a,b+c+d,e)`. -/
noncomputable def gV4AssocC :
    RelTensor K (Γ.D (b + c + d)).carrier (GBL Γ b c d)
        (RelTensor K (Γ.D (a + b + c + d)).carrier (FusionColumn (Γ.fuse a (b + c + d)))
          (FusionColumn (Γ.fuse (a + b + c + d) e))) ≃ₗ[K]
      RelTensor K (Γ.D (b + c + d)).carrier (GBL Γ b c d) (GBL Γ a (b + c + d) e) :=
  RelTensor.mapEquivRight K (gFourCast K Γ a b c d e) (gFourCast_midSlot K Γ a b c d e)

/-- **`gV4Assoc`**: `V4`'s own re-association, exposing `GBL(b,c,d)
⊗_{D_{b+c+d}} GBL(a,b+c+d,e)` — the composite of stages A, B, C. -/
noncomputable def gV4Assoc : V4 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (b + c + d)).carrier (GBL Γ b c d) (GBL Γ a (b + c + d) e) :=
  (gV4AssocA K Γ a b c d e).trans ((gV4AssocB K Γ a b c d e).trans (gV4AssocC K Γ a b c d e))

/-- The signed `(b+c+d)`-slot (middle-slot) whiskering of `gTCanon Γ a
(b+c+d) e`, landing `V10`'s own `GBR(a,b+c+d,e)` factor. -/
noncomputable def gE15Step :
    RelTensor K (Γ.D (b + c + d)).carrier (GBL Γ b c d) (GBL Γ a (b + c + d) e) ≃ₗ[K]
      RelTensor K (Γ.D (b + c + d)).carrier (GBL Γ b c d) (GBR Γ a (b + c + d) e) :=
  PentagonB.smapEquiv K (Γ.D (b + c + d)).grading (GBL.grading Γ b c d)
    (gTCanon K Γ a (b + c + d) e) (gParity K Γ a (b + c + d) e) (gCanonMidSlot K Γ a (b + c + d) e)

/-- **`E15M`, as a `LinearEquiv`**: `gV4Assoc` then the signed
`(b+c+d)`-slot amplification, then `gV10Assoc⁻¹`. -/
noncomputable def E15Mequiv : V4 K Γ a b c d e ≃ₗ[K] V10 K Γ a b c d e :=
  ((gV4Assoc K Γ a b c d e).trans (gE15Step K Γ a b c d e)).trans (gV10Assoc K Γ a b c d e).symm

/-- **Edge 15** `E15M : V4 → V10`, `t_{a,b+c+d,e}` (owning faces `PBC`,
`S2`; presentation: `S2`, `gV4Assoc` then the whiskered `gTCanon Γ a
(b+c+d) e` then `gV10Assoc⁻¹`). -/
noncomputable def E15M : V4 K Γ a b c d e →ₗ[K] V10 K Γ a b c d e :=
  (E15Mequiv K Γ a b c d e).toLinearMap

theorem E15M_bijective : Function.Bijective (E15M K Γ a b c d e) :=
  (E15Mequiv K Γ a b c d e).bijective

end GaugeChi

end Superfusion
