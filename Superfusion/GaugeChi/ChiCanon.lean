/-
Superfusion / GaugeChi / ChiCanon

Milestone M12-11 of the abstract `(p, χ)` arc: **`gParity_cocycle`** — the
Gu–Wen parity cocycle condition, canonical and Skolem–Noether-free, for
every division fusion gauge — and **`gChiCanon`**, `gChi` instantiated at
the canonical data `exists_gIntertwiner` supplies at the five pentagon
triples.  The Γ-mirror of `Superfusion.Bimod.ChiCanon`, one abstraction
level up (no matrix frames, no Skolem–Noether: the triple-level canonical
data is `exists_gIntertwiner`/`gIntertwiner_bijective`,
`GaugeChi.GaugeParity`, already landed).

**`gColumnCastFst`**: casting a fusion column's *first* index — the
Γ-mirror of `Bimod.ChiCanon`'s `columnCastFst` (the mirror image of
`Pentagon.lean`'s own `fusionColumnCast`, which casts the *second* index).

**`gq2rCast : GQ2rInner K Γ a b c d ≃ₗ[K] GBL Γ a (b + c) d`**: built
exactly as `Pentagon.lean`'s `gq4Close`'s recast leg — two `RelTensor.lift`
legs glued by `LinearEquiv.ofLinear`, identity on the shared first factor
`F_{a,b+c}`, `gColumnCastFst` on the second.  `GQ3Inner K Γ a b c d` needs
no such recast (`b + c + d` and `(b + c) + d` are the same term).

**`gt2Canon φ := gq2rCast.trans φ`**, for any canonical
`φ : GBL Γ a (b+c) d ≃ₗ[K] GBR Γ a (b+c) d`: `gTopRoute`'s second-edge
candidate, with its four raw conditions transported through `gq2rCast`
from `φ`'s own `gInterSpace` membership, exactly as `Bimod.ChiCanon`'s
`t2Canon` transports `tCanonEquiv`'s.

**`gParity_cocycle`**: assembled directly from first principles (no
Skolem–Noether detour through a separate concrete `pentagonParity`): the
canonical top route (at `exists_gIntertwiner`'s data for the triples
`(a,b,c)`, `(a,b+c,d)`, `(b,c,d)`, via `gt2Canon`) and the canonical bottom
route (at `(a+b,c,d)`, `(a,b,c+d)`) are BOTH nonzero members of
`gQuadInterSpace K Γ a b c d` — the top route at degree `gParity Γ a b c +
gParity Γ a (b+c) d + gParity Γ b c d`, the bottom route at degree
`gParity Γ (a+b) c d + gParity Γ a b (c+d)` — and `gQuadInterSpace`'s total
dimension is `≤ 1` (deliverables 1–2), so two nonzero members force their
degrees to coincide.

**`gChiCanon`**: `gChi` instantiated at this canonical data, with `he`
discharged by `gParity_cocycle`.  THE paper's `χ`, defined canonically
from bimodule isomorphism data over any division fusion gauge — no
Skolem–Noether, no matrix frames; unique up to the intertwiner
normalizations (a coboundary).
-/
import Superfusion.GaugeChi.ChiAbs

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c d : G)

attribute [local instance 500] leftModule rightModule

/-! ### `gColumnCastFst`: casting a fusion column's *first* index

The mirror image of `Pentagon.lean`'s `fusionColumnCast` (which casts the
*second* index, first index fixed): here the *second* index `d` is fixed
and the *first* index is cast along an equality, via the same `subst`
device — the Γ-mirror of `Bimod.ChiCanon`'s `columnCastFst`. -/

/-- **Casting a fusion column's first index**: `FusionColumn (Γ.fuse x d)
≃ₗ[K] FusionColumn (Γ.fuse y d)` given `x = y`, by `subst`. -/
noncomputable def gColumnCastFst (d : G) {x y : G} (h : x = y) :
    FusionColumn (Γ.fuse x d) ≃ₗ[K] FusionColumn (Γ.fuse y d) := by
  subst h
  exact LinearEquiv.refl K _

/-- The untouched `d`-slot (second index) commutes trivially with the
cast. -/
theorem gColumnCastFst_dslot {x y : G} (h : x = y) (d : G)
    (t : (Γ.D d).carrier) (w : FusionColumn (Γ.fuse x d)) :
    gColumnCastFst K Γ d h (t • w) = t • gColumnCastFst K Γ d h w := by
  subst h
  rfl

/-- The *cast* slot's own native action (the column's first-index action,
matching `x`) transports along `Γ.gaugeCast`. -/
theorem gColumnCastFst_xslot {x y : G} (h : x = y) (d : G)
    (τ : (Γ.D x).carrier) (w : FusionColumn (Γ.fuse x d)) :
    gColumnCastFst K Γ d h (τ • w)
      = (Γ.gaugeCast h).toAlgEquiv τ • gColumnCastFst K Γ d h w := by
  subst h
  rfl

/-- The inverse cast's mirror of `gColumnCastFst_xslot`. -/
theorem gColumnCastFst_symm_xslot {x y : G} (h : x = y) (d : G)
    (τ : (Γ.D y).carrier) (w : FusionColumn (Γ.fuse y d)) :
    (gColumnCastFst K Γ d h).symm (τ • w)
      = (Γ.gaugeCast h).toAlgEquiv.symm τ • (gColumnCastFst K Γ d h).symm w := by
  subst h
  rfl

/-- The natural coefficient (right) action transports along the induced
sum-level tower cast. -/
theorem gColumnCastFst_coeff {x y : G} (h : x = y) (d : G)
    (τ : (Γ.D (x + d)).carrier) (w : FusionColumn (Γ.fuse x d)) :
    gColumnCastFst K Γ d h (MulOpposite.op τ • w)
      = MulOpposite.op ((Γ.gaugeCast (congrArg (· + d) h)).toAlgEquiv τ)
          • gColumnCastFst K Γ d h w := by
  subst h
  rfl

/-- The column cast preserves the descended grading. -/
theorem gColumnCastFst_mem_grading {x y : G} (h : x = y) (d : G) {j : ZMod 2}
    {w : FusionColumn (Γ.fuse x d)} (hw : w ∈ FusionColumn.grading (Γ.fuse x d) j) :
    gColumnCastFst K Γ d h w ∈ FusionColumn.grading (Γ.fuse y d) j := by
  subst h
  exact hw

/-! ### `gq2rCast`: the recast `GQ2rInner K Γ a b c d ≃ₗ[K] GBL Γ a (b + c) d`

Built exactly as `Pentagon.lean`'s `gq4Close`'s recast leg: two
`RelTensor.lift` legs glued by `LinearEquiv.ofLinear`, identity on the
shared first factor `F_{a,b+c}`, `gColumnCastFst` on the second. -/

private noncomputable def gq2rFwdBilin :
    FusionColumn (Γ.fuse a (b + c)) →ₗ[K]
      FusionColumn (Γ.fuse (a + b + c) d) →ₗ[K] GBL Γ a (b + c) d :=
  (GBL.mk Γ a (b + c) d).compl₂ (gColumnCastFst K Γ d (add_assoc a b c)).toLinearMap

private theorem gq2rFwdBilin_apply (v : FusionColumn (Γ.fuse a (b + c)))
    (w : FusionColumn (Γ.fuse (a + b + c) d)) :
    gq2rFwdBilin K Γ a b c d v w
      = GBL.mk Γ a (b + c) d v (gColumnCastFst K Γ d (add_assoc a b c) w) := rfl

private theorem GBL_mk_eq (v : FusionColumn (Γ.fuse a (b + c)))
    (w : FusionColumn (Γ.fuse (a + (b + c)) d)) :
    GBL.mk Γ a (b + c) d v w
      = RelTensor.mk K (Γ.D (a + (b + c))).carrier
          (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + (b + c)) d)) v w := rfl

private theorem gq2rFwd_balanced :
    RelTensor.IsBalanced (Γ.D (a + b + c)).carrier (gq2rFwdBilin K Γ a b c d) := by
  intro t v w
  rw [gq2rFwdBilin_apply, gq2rFwdBilin_apply, gColumnCastFst_xslot, GBL_mk_eq, GBL_mk_eq,
    fusionColumn_recast_op_smul_def, RelTensor.mk_op_smul]

private noncomputable def gq2rFwd : GQ2rInner K Γ a b c d →ₗ[K] GBL Γ a (b + c) d :=
  RelTensor.lift (gq2rFwdBilin K Γ a b c d) (gq2rFwd_balanced K Γ a b c d)

private theorem gq2rFwd_mk (v : FusionColumn (Γ.fuse a (b + c)))
    (w : FusionColumn (Γ.fuse (a + b + c) d)) :
    gq2rFwd K Γ a b c d (RelTensor.mk K (Γ.D (a + b + c)).carrier
        (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w)
      = GBL.mk Γ a (b + c) d v (gColumnCastFst K Γ d (add_assoc a b c) w) := by
  show RelTensor.lift (gq2rFwdBilin K Γ a b c d) (gq2rFwd_balanced K Γ a b c d)
      (RelTensor.mk K (Γ.D (a + b + c)).carrier
        (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w) = _
  rw [RelTensor.lift_mk, gq2rFwdBilin_apply]

private noncomputable def gq2rBwdBilin :
    FusionColumn (Γ.fuse a (b + c)) →ₗ[K]
      FusionColumn (Γ.fuse (a + (b + c)) d) →ₗ[K] GQ2rInner K Γ a b c d :=
  (RelTensor.mk K (Γ.D (a + b + c)).carrier
      (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d))).compl₂
    (gColumnCastFst K Γ d (add_assoc a b c)).symm.toLinearMap

private theorem gq2rBwdBilin_apply (v : FusionColumn (Γ.fuse a (b + c)))
    (w : FusionColumn (Γ.fuse (a + (b + c)) d)) :
    gq2rBwdBilin K Γ a b c d v w
      = RelTensor.mk K (Γ.D (a + b + c)).carrier
          (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v
          ((gColumnCastFst K Γ d (add_assoc a b c)).symm w) := rfl

private theorem gq2rBwd_balanced :
    RelTensor.IsBalanced (Γ.D (a + (b + c))).carrier (gq2rBwdBilin K Γ a b c d) := by
  intro s v w
  rw [gq2rBwdBilin_apply, gq2rBwdBilin_apply, gColumnCastFst_symm_xslot,
    show (MulOpposite.op s • v : FusionColumn (Γ.fuse a (b + c)))
        = MulOpposite.op ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv.symm s) • v from by
      rw [fusionColumn_recast_op_smul_def, AlgEquiv.apply_symm_apply],
    RelTensor.mk_op_smul]

private noncomputable def gq2rBwd : GBL Γ a (b + c) d →ₗ[K] GQ2rInner K Γ a b c d :=
  RelTensor.lift (gq2rBwdBilin K Γ a b c d) (gq2rBwd_balanced K Γ a b c d)

private theorem gq2rBwd_mk (v : FusionColumn (Γ.fuse a (b + c)))
    (w : FusionColumn (Γ.fuse (a + (b + c)) d)) :
    gq2rBwd K Γ a b c d (GBL.mk Γ a (b + c) d v w)
      = RelTensor.mk K (Γ.D (a + b + c)).carrier
          (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v
          ((gColumnCastFst K Γ d (add_assoc a b c)).symm w) := by
  show RelTensor.lift (gq2rBwdBilin K Γ a b c d) (gq2rBwd_balanced K Γ a b c d)
      (RelTensor.mk K (Γ.D (a + (b + c))).carrier
        (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + (b + c)) d)) v w) = _
  rw [RelTensor.lift_mk, gq2rBwdBilin_apply]

private theorem gq2rFwd_bwd :
    (gq2rFwd K Γ a b c d).comp (gq2rBwd K Γ a b c d) = LinearMap.id := by
  refine RelTensor.hom_ext fun v w => ?_
  show gq2rFwd K Γ a b c d (gq2rBwd K Γ a b c d (GBL.mk Γ a (b + c) d v w))
    = GBL.mk Γ a (b + c) d v w
  rw [gq2rBwd_mk, gq2rFwd_mk, LinearEquiv.apply_symm_apply]

private theorem gq2rBwd_fwd :
    (gq2rBwd K Γ a b c d).comp (gq2rFwd K Γ a b c d) = LinearMap.id := by
  refine RelTensor.hom_ext fun v w => ?_
  show gq2rBwd K Γ a b c d (gq2rFwd K Γ a b c d (RelTensor.mk K (Γ.D (a + b + c)).carrier
      (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w))
    = RelTensor.mk K (Γ.D (a + b + c)).carrier
        (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w
  rw [gq2rFwd_mk, gq2rBwd_mk, LinearEquiv.symm_apply_apply]

/-- **The recast** `GQ2rInner K Γ a b c d ≃ₗ[K] GBL Γ a (b + c) d`:
identity on the shared first factor `F_{a,b+c}`, `gColumnCastFst` on the
second — the associativity recast of the second pentagon edge's domain. -/
noncomputable def gq2rCast : GQ2rInner K Γ a b c d ≃ₗ[K] GBL Γ a (b + c) d :=
  LinearEquiv.ofLinear (gq2rFwd K Γ a b c d) (gq2rBwd K Γ a b c d)
    (gq2rFwd_bwd K Γ a b c d) (gq2rBwd_fwd K Γ a b c d)

theorem gq2rCast_mk (v : FusionColumn (Γ.fuse a (b + c)))
    (w : FusionColumn (Γ.fuse (a + b + c) d)) :
    gq2rCast K Γ a b c d (RelTensor.mk K (Γ.D (a + b + c)).carrier
        (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w)
      = GBL.mk Γ a (b + c) d v (gColumnCastFst K Γ d (add_assoc a b c) w) :=
  gq2rFwd_mk K Γ a b c d v w

/-! ### `gq2rCast`'s two unconditional commutation laws -/

private theorem gq2rInner_dSlot_mk (τ : (Γ.D d).carrier)
    (v : FusionColumn (Γ.fuse a (b + c))) (w : FusionColumn (Γ.fuse (a + b + c) d)) :
    (τ • (RelTensor.mk K (Γ.D (a + b + c)).carrier
        (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w)
      : GQ2rInner K Γ a b c d)
      = midBilin (FusionColumn.grading (Γ.fuse a (b + c))) (Γ.D d).grading τ v w :=
  midEnd_mk (Γ.D (a + b + c)).grading (FusionColumn.grading (Γ.fuse a (b + c)))
    (Γ.D d).grading (FusionColumn.superCommSMul (Γ.fuse (a + b + c) d)) τ v w

private theorem gbl_dSlot_mk (τ : (Γ.D d).carrier)
    (v : FusionColumn (Γ.fuse a (b + c))) (w : FusionColumn (Γ.fuse (a + (b + c)) d)) :
    (τ • GBL.mk Γ a (b + c) d v w : GBL Γ a (b + c) d)
      = midBilin (FusionColumn.grading (Γ.fuse a (b + c))) (Γ.D d).grading τ v w :=
  midEnd_mk (Γ.D (a + (b + c))).grading (FusionColumn.grading (Γ.fuse a (b + c)))
    (Γ.D d).grading (FusionColumn.superCommSMul (Γ.fuse (a + (b + c)) d)) τ v w

/-- **`gq2rCast` commutes with the `(b+c)`-slot action, unconditionally**
(no degree hypothesis, no sign): the action only ever touches the
untouched first factor `F_{a,b+c}`. -/
theorem gq2rCast_bcSlot (y : (Γ.D (b + c)).carrier) (n : GQ2rInner K Γ a b c d) :
    gq2rCast K Γ a b c d (y • n) = y • gq2rCast K Γ a b c d n := by
  induction n using RelTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | mk v w =>
      have hR : y • gq2rCast K Γ a b c d (RelTensor.mk K (Γ.D (a + b + c)).carrier
          (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w)
        = GBL.mk Γ a (b + c) d (y • v) (gColumnCastFst K Γ d (add_assoc a b c) w) := by
        rw [gq2rCast_mk, GBL.bslot_smul_mk]
      have hL : gq2rCast K Γ a b c d (y • RelTensor.mk K (Γ.D (a + b + c)).carrier
          (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w)
        = GBL.mk Γ a (b + c) d (y • v) (gColumnCastFst K Γ d (add_assoc a b c) w) := by
        rw [show (y • RelTensor.mk K (Γ.D (a + b + c)).carrier
              (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w
              : GQ2rInner K Γ a b c d)
            = RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                (FusionColumn (Γ.fuse (a + b + c) d)) (y • v) w from
          leftActionEnd_mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
            (FusionColumn (Γ.fuse (a + b + c) d)) y v w,
          gq2rCast_mk]
      rw [hL, hR]
  | add x y' hx hy' => rw [smul_add, map_add, map_add, smul_add, hx, hy']

/-- **`gq2rCast` commutes with the `d`-slot action, unconditionally**
(no degree hypothesis, no sign): the `midBilin` expansion only ever
touches `F_{a+b+c,d}`'s own native `d`-slot, transported cleanly by
`gColumnCastFst_dslot`. -/
theorem gq2rCast_dSlot (τ : (Γ.D d).carrier) (n : GQ2rInner K Γ a b c d) :
    gq2rCast K Γ a b c d (τ • n) = τ • gq2rCast K Γ a b c d n := by
  induction n using RelTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | mk v w =>
      have hR : τ • gq2rCast K Γ a b c d (RelTensor.mk K (Γ.D (a + b + c)).carrier
          (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w)
        = midBilin (FusionColumn.grading (Γ.fuse a (b + c))) (Γ.D d).grading τ v
            (gColumnCastFst K Γ d (add_assoc a b c) w) := by
        rw [gq2rCast_mk, gbl_dSlot_mk]
      have hL : gq2rCast K Γ a b c d (τ • RelTensor.mk K (Γ.D (a + b + c)).carrier
          (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w)
        = midBilin (FusionColumn.grading (Γ.fuse a (b + c))) (Γ.D d).grading τ v
            (gColumnCastFst K Γ d (add_assoc a b c) w) := by
        rw [gq2rInner_dSlot_mk, midBilin_apply, map_sub, map_zsmul, gq2rCast_mk, gq2rCast_mk,
          gColumnCastFst_dslot, gColumnCastFst_dslot, GBL_mk_eq, GBL_mk_eq, midBilin_apply]
        rfl
      rw [hL, hR]
  | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]

/-! ### `gq2rCast`'s gradedness -/

/-- **`gq2rCast` preserves the descended grading**:
`Bimod.RelTensor.mem_of_grading` (general, already reused throughout
`PentagonRouteMembership.lean`) applied at `gq2rCast`'s own construction. -/
theorem gq2rCast_mem_grading {jj : ZMod 2} {n : GQ2rInner K Γ a b c d}
    (hn : n ∈ relGrading (Γ.D (a + b + c)).carrier
        (FusionColumn.grading (Γ.fuse a (b + c))) (FusionColumn.grading (Γ.fuse (a + b + c) d))
        jj) :
    gq2rCast K Γ a b c d n ∈ GBL.grading Γ a (b + c) d jj := by
  refine Superfusion.Bimod.RelTensor.mem_of_grading
    (FusionColumn.grading (Γ.fuse a (b + c)))
    (FusionColumn.grading (Γ.fuse (a + b + c) d)) (gq2rCast K Γ a b c d).toLinearMap
    (GBL.grading Γ a (b + c) d jj) hn ?_
  intro j k hjk v w hv hw
  show gq2rCast K Γ a b c d (RelTensor.mk K (Γ.D (a + b + c)).carrier
      (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w)
    ∈ GBL.grading Γ a (b + c) d jj
  rw [gq2rCast_mk]
  subst hjk
  exact GBL.mk_mem_grading Γ a (b + c) d hv (gColumnCastFst_mem_grading K Γ (add_assoc a b c) d hw)

/-! ### `gTCanon`: the canonical triple intertwiner, at any triple -/

/-- **`gTCanon Γ x y z`**: the canonical intertwiner `GBL Γ x y z ≃ₗ[K]
GBR Γ x y z`, at its own pentagon degree `gParity Γ x y z` — the
`Exists.choose` of `exists_gIntertwiner`, upgraded to a `LinearEquiv` via
`gIntertwiner_bijective`. -/
noncomputable def gTCanon (x y z : G) : GBL Γ x y z ≃ₗ[K] GBR Γ x y z :=
  LinearEquiv.ofBijective (exists_gIntertwiner K Γ x y z).choose
    (gIntertwiner_bijective K Γ x y z (exists_gIntertwiner K Γ x y z).choose_spec.1
      (exists_gIntertwiner K Γ x y z).choose_spec.2)

theorem gTCanon_mem_gInterSpace (x y z : G) :
    (gTCanon K Γ x y z).toLinearMap ∈ gInterSpace K Γ x y z (gParity K Γ x y z) :=
  (exists_gIntertwiner K Γ x y z).choose_spec.1

/-! ### `gt2Canon`: the canonical second-edge intertwiner -/

/-- **`gt2Canon`**: the canonical second-edge intertwiner `GQ2rInner K Γ a
b c d ≃ₗ[K] GQ3Inner K Γ a b c d` — `gq2rCast` followed by any
`φ : GBL Γ a (b+c) d ≃ₗ[K] GBR Γ a (b+c) d` (whose codomain `GBR Γ a (b+c)
d` is *literally* `GQ3Inner K Γ a b c d`, `Pentagon.lean`'s
`inferInstanceAs` bridges — `b + c + d` and `(b + c) + d` are the same
term). -/
noncomputable def gt2Canon (φ : GBL Γ a (b + c) d ≃ₗ[K] GBR Γ a (b + c) d) :
    GQ2rInner K Γ a b c d ≃ₗ[K] GQ3Inner K Γ a b c d :=
  (gq2rCast K Γ a b c d).trans φ

theorem gt2Canon_mk (φ : GBL Γ a (b + c) d ≃ₗ[K] GBR Γ a (b + c) d)
    (v : FusionColumn (Γ.fuse a (b + c))) (w : FusionColumn (Γ.fuse (a + b + c) d)) :
    gt2Canon K Γ a b c d φ (RelTensor.mk K (Γ.D (a + b + c)).carrier
        (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w)
      = φ (GBL.mk Γ a (b + c) d v (gColumnCastFst K Γ d (add_assoc a b c) w)) := by
  show φ (gq2rCast K Γ a b c d (RelTensor.mk K (Γ.D (a + b + c)).carrier
      (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w)) = _
  rw [gq2rCast_mk]

variable {a b c d}

/-! ### `gt2Canon`'s five raw conditions -/

/-- **The `(b+c)`-slot equivariance**: `gq2rCast_bcSlot` composed with
`φ`'s own `(b+c)`-slot condition (`gInterSpace K Γ a (b+c) d`'s second
`superEquivariant` conjunct). -/
theorem gt2Canon_bcSlot (φ : GBL Γ a (b + c) d ≃ₗ[K] GBR Γ a (b + c) d) (e : ZMod 2)
    (hφ : φ.toLinearMap ∈ gInterSpace K Γ a (b + c) d e) :
    ∀ ⦃i : ZMod 2⦄ ⦃y : (Γ.D (b + c)).carrier⦄,
      y ∈ (Γ.D (b + c)).grading i → ∀ n : GQ2rInner K Γ a b c d,
        gt2Canon K Γ a b c d φ (y • n)
          = ((sgn (e * i) : ℤˣ) : ℤ) • (y • gt2Canon K Γ a b c d φ n) := by
  intro i y hy n
  show φ (gq2rCast K Γ a b c d (y • n))
    = ((sgn (e * i) : ℤˣ) : ℤ) • (y • φ (gq2rCast K Γ a b c d n))
  rw [gq2rCast_bcSlot]
  exact (mem_superEquivariant (Γ.D (b + c)).grading).mp
    ((mem_gInterSpace_iff K Γ a (b + c) d).mp hφ).2.2.1 hy (gq2rCast K Γ a b c d n)

/-- **The raw `a`-slot equivariance**, at generator level. -/
theorem gt2Canon_aSlot (φ : GBL Γ a (b + c) d ≃ₗ[K] GBR Γ a (b + c) d) (e : ZMod 2)
    (hφ : φ.toLinearMap ∈ gInterSpace K Γ a (b + c) d e) :
    ∀ ⦃k : ZMod 2⦄ ⦃x : (Γ.D a).carrier⦄,
      x ∈ (Γ.D a).grading k →
      ∀ (v : FusionColumn (Γ.fuse a (b + c))) (w : FusionColumn (Γ.fuse (a + b + c) d)),
        gt2Canon K Γ a b c d φ (RelTensor.mk K (Γ.D (a + b + c)).carrier
              (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) (x • v) w)
          = ((sgn (e * k) : ℤˣ) : ℤ) •
              (x • gt2Canon K Γ a b c d φ (RelTensor.mk K (Γ.D (a + b + c)).carrier
                (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w)) := by
  intro k x hx v w
  have ha := (mem_superEquivariant (Γ.D a).grading).mp
    ((mem_gInterSpace_iff K Γ a (b + c) d).mp hφ).2.1 hx
    (GBL.mk Γ a (b + c) d v (gColumnCastFst K Γ d (add_assoc a b c) w))
  rw [gt2Canon_mk, gt2Canon_mk, ← GBL.aslot_smul_mk]
  exact ha

/-- **The raw `d`-slot equivariance**: `gq2rCast_dSlot` composed with `φ`'s
own `d`-slot condition. -/
theorem gt2Canon_dSlot (φ : GBL Γ a (b + c) d ≃ₗ[K] GBR Γ a (b + c) d) (e : ZMod 2)
    (hφ : φ.toLinearMap ∈ gInterSpace K Γ a (b + c) d e) :
    ∀ ⦃m : ZMod 2⦄ ⦃τ : (Γ.D d).carrier⦄,
      τ ∈ (Γ.D d).grading m → ∀ x : GQ2rInner K Γ a b c d,
        gt2Canon K Γ a b c d φ (τ • x)
          = ((sgn (e * m) : ℤˣ) : ℤ) • (τ • gt2Canon K Γ a b c d φ x) := by
  intro m τ hτ n
  show φ (gq2rCast K Γ a b c d (τ • n))
    = ((sgn (e * m) : ℤˣ) : ℤ) • (τ • φ (gq2rCast K Γ a b c d n))
  rw [gq2rCast_dSlot]
  exact (mem_superEquivariant (Γ.D d).grading).mp
    ((mem_gInterSpace_iff K Γ a (b + c) d).mp hφ).2.2.2.1 hτ (gq2rCast K Γ a b c d n)

/-- The associativity recast of the total coefficient algebra used by
`gt2Canon_rightSlot`. -/
private theorem right_recast_eq' : a + b + c + d = a + (b + c + d) := by
  rw [add_assoc, add_assoc, add_assoc]

/-- Two composed `Γ.gaugeCast`s along a chain `x = y = z` collapse to the
single cast along the transitivity, by `subst`. -/
private theorem gaugeCast_trans {x y z : G} (h1 : x = y) (h2 : y = z)
    (τ : (Γ.D x).carrier) :
    (Γ.gaugeCast h2).toAlgEquiv ((Γ.gaugeCast h1).toAlgEquiv τ)
      = (Γ.gaugeCast (h1.trans h2)).toAlgEquiv τ := by
  subst h1
  subst h2
  rfl

/-- **The raw right-equivariance**, at generator level — the two composed
casts (`gColumnCastFst_coeff`'s induced sum-level cast, then `GBL`/`GBR`'s
own associativity cast) collapse, via `gaugeCast_trans` and proof
irrelevance, to the single cast `a + b + c + d = a + (b + c + d)` this
condition is stated against. -/
theorem gt2Canon_rightSlot (φ : GBL Γ a (b + c) d ≃ₗ[K] GBR Γ a (b + c) d) (e : ZMod 2)
    (hφ : φ.toLinearMap ∈ gInterSpace K Γ a (b + c) d e) :
    ∀ (τ : (Γ.D (a + b + c + d)).carrier)
      (v : FusionColumn (Γ.fuse a (b + c))) (w : FusionColumn (Γ.fuse (a + b + c) d)),
      gt2Canon K Γ a b c d φ (RelTensor.mk K (Γ.D (a + b + c)).carrier
            (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v
            (MulOpposite.op τ • w))
        = MulOpposite.op ((Γ.gaugeCast right_recast_eq').toAlgEquiv τ)
            • gt2Canon K Γ a b c d φ (RelTensor.mk K (Γ.D (a + b + c)).carrier
            (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w) := by
  intro τ v w
  have hR : φ (MulOpposite.op ((Γ.gaugeCast (congrArg (· + d) (add_assoc a b c))).toAlgEquiv τ)
        • GBL.mk Γ a (b + c) d v (gColumnCastFst K Γ d (add_assoc a b c) w))
    = MulOpposite.op ((Γ.gaugeCast (congrArg (· + d) (add_assoc a b c))).toAlgEquiv τ)
        • φ (GBL.mk Γ a (b + c) d v (gColumnCastFst K Γ d (add_assoc a b c) w)) :=
    (mem_rightSemilinear
        (ψ := (Γ.gaugeCast (add_assoc a (b + c) d)).toAlgEquiv.toAlgHom.toRingHom)).mp
      ((mem_gInterSpace_iff K Γ a (b + c) d).mp hφ).2.2.2.2
      ((Γ.gaugeCast (congrArg (· + d) (add_assoc a b c))).toAlgEquiv τ)
      (GBL.mk Γ a (b + c) d v (gColumnCastFst K Γ d (add_assoc a b c) w))
  rw [gt2Canon_mk, gt2Canon_mk, gColumnCastFst_coeff, ← GBL.right_smul_mk, hR,
    GBR.recast_op_smul_def, gaugeCast_trans]
  rfl

/-- **`gt2Canon`'s degree-`e` homogeneity** — `gq2rCast_mem_grading`
composed with `φ`'s own `homGrading` condition. -/
theorem gt2Canon_mem_grading (φ : GBL Γ a (b + c) d ≃ₗ[K] GBR Γ a (b + c) d) (e : ZMod 2)
    (hφ : φ.toLinearMap ∈ gInterSpace K Γ a (b + c) d e) :
    ∀ jj : ZMod 2,
      ∀ n ∈ relGrading (Γ.D (a + b + c)).carrier
          (FusionColumn.grading (Γ.fuse a (b + c))) (FusionColumn.grading (Γ.fuse (a + b + c) d))
          jj,
        gt2Canon K Γ a b c d φ n ∈ GQ3Inner.grading K Γ a b c d (jj + e) := by
  intro jj n hn
  exact (mem_homGrading (GBL.grading Γ a (b + c) d) (GBR.grading Γ a (b + c) d)).mp
    ((mem_gInterSpace_iff K Γ a (b + c) d).mp hφ).1
    jj (gq2rCast K Γ a b c d n) (gq2rCast_mem_grading K Γ a b c d hn)

variable (a b c d)

/-! ### `gParity_cocycle`: THE Gu–Wen parity cocycle condition -/

/-- The right-recast equivariance of `gTCanon Γ x y z`, bridged from
`gTCanon_mem_gInterSpace`'s `rightSemilinear` conjunct. -/
private theorem canon_right (x y z : G) :
    ∀ (τ : (Γ.D (x + y + z)).carrier) (m : GBL Γ x y z),
      gTCanon K Γ x y z (MulOpposite.op τ • m) = MulOpposite.op τ • gTCanon K Γ x y z m :=
  (mem_rightSemilinear
      (ψ := (Γ.gaugeCast (add_assoc x y z)).toAlgEquiv.toAlgHom.toRingHom)).mp
    ((mem_gInterSpace_iff K Γ x y z).mp (gTCanon_mem_gInterSpace K Γ x y z)).2.2.2.2

/-- The signed `(x+y)`-slot equivariance of `gTCanon Γ (x+y) z w`. -/
private theorem canon_hφ₄ (x y z w : G) :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (x + y)).carrier⦄,
      τ ∈ (Γ.D (x + y)).grading i → ∀ n : GBL Γ (x + y) z w,
        gTCanon K Γ (x + y) z w (τ • n)
          = ((sgn (gParity K Γ (x + y) z w * i) : ℤˣ) : ℤ) • (τ • gTCanon K Γ (x + y) z w n) :=
  (mem_superEquivariant (Γ.D (x + y)).grading).mp
    ((mem_gInterSpace_iff K Γ (x + y) z w).mp (gTCanon_mem_gInterSpace K Γ (x + y) z w)).2.1

/-- The signed `(z+w)`-slot equivariance of `gTCanon Γ x y (z+w)`. -/
private theorem canon_hφ₅ (x y z w : G) :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (z + w)).carrier⦄,
      τ ∈ (Γ.D (z + w)).grading i → ∀ n : GBL Γ x y (z + w),
        gTCanon K Γ x y (z + w) (τ • n)
          = ((sgn (gParity K Γ x y (z + w) * i) : ℤˣ) : ℤ) • (τ • gTCanon K Γ x y (z + w) n) :=
  (mem_superEquivariant (Γ.D (z + w)).grading).mp
    ((mem_gInterSpace_iff K Γ x y (z + w)).mp (gTCanon_mem_gInterSpace K Γ x y (z + w))).2.2.2.1

/-- **`gParity_cocycle`**: THE Gu–Wen parity cocycle condition, canonical
and Skolem–Noether-free, for every division fusion gauge `Γ` — the
canonical top route (at `gTCanon Γ a b c`, `gt2Canon (gTCanon Γ a (b+c)
d)`, `gTCanon Γ b c d`) and the canonical bottom route (at `gTCanon Γ
(a+b) c d`, `gTCanon Γ a b (c+d)`) are BOTH nonzero members of
`gQuadInterSpace K Γ a b c d`, at their own naturally-computed degrees;
`gQuadInterSpace`'s total dimension `≤ 1` forces the two degrees to
coincide. -/
theorem gParity_cocycle :
    gParity K Γ a b c + gParity K Γ a (b + c) d + gParity K Γ b c d
      = gParity K Γ (a + b) c d + gParity K Γ a b (c + d) := by
  haveI := gq1_finite K Γ a b c d
  haveI := gq1_nontrivial K Γ a b c d
  set φ₁ := gTCanon K Γ a b c with hφ₁def
  set φ₂ := gt2Canon K Γ a b c d (gTCanon K Γ a (b + c) d) with hφ₂def
  set φ₃ := gTCanon K Γ b c d with hφ₃def
  set φ₄ := gTCanon K Γ (a + b) c d with hφ₄def
  set φ₅ := gTCanon K Γ a b (c + d) with hφ₅def
  have hφ₂equiv := gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) d)
    (gParity K Γ a (b + c) d) (gTCanon_mem_gInterSpace K Γ a (b + c) d)
  have htopbij : Function.Bijective
      (gTopRoute K Γ a b c d φ₁.toLinearMap (canon_right K Γ a b c) (gParity K Γ a (b + c) d)
        φ₂.toLinearMap hφ₂equiv φ₃.toLinearMap (canon_right K Γ b c d)) :=
    gTopRoute_bijective K Γ a b c d φ₁ (canon_right K Γ a b c) (gParity K Γ a (b + c) d) φ₂
      hφ₂equiv φ₃ (canon_right K Γ b c d)
  have htopne := gTopRoute_ne_zero_of_bijective K Γ a b c d φ₁.toLinearMap (canon_right K Γ a b c)
    (gParity K Γ a (b + c) d) φ₂.toLinearMap hφ₂equiv φ₃.toLinearMap (canon_right K Γ b c d) htopbij
  have htopmem := gTopRoute_mem K Γ a b c d φ₁.toLinearMap (canon_right K Γ a b c)
      (gParity K Γ a (b + c) d) φ₂.toLinearMap hφ₂equiv φ₃.toLinearMap (canon_right K Γ b c d)
    (gTCanon_mem_gInterSpace K Γ a b c)
    (gt2Canon_aSlot K Γ (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
      (gTCanon_mem_gInterSpace K Γ a (b + c) d))
    (gt2Canon_dSlot K Γ (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
      (gTCanon_mem_gInterSpace K Γ a (b + c) d))
    (gt2Canon_rightSlot K Γ (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
      (gTCanon_mem_gInterSpace K Γ a (b + c) d))
    (gt2Canon_mem_grading K Γ (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
      (gTCanon_mem_gInterSpace K Γ a (b + c) d))
    (gTCanon_mem_gInterSpace K Γ b c d)
  have hbotbij : Function.Bijective
      (gBotRoute K Γ a b c d (gParity K Γ (a + b) c d) φ₄.toLinearMap (canon_hφ₄ K Γ a b c d)
        (gParity K Γ a b (c + d)) φ₅.toLinearMap (canon_hφ₅ K Γ a b c d)) :=
    gBotRoute_bijective K Γ a b c d (gParity K Γ (a + b) c d) φ₄ (canon_hφ₄ K Γ a b c d)
      (gParity K Γ a b (c + d)) φ₅ (canon_hφ₅ K Γ a b c d)
  have hbotne := gBotRoute_ne_zero_of_bijective K Γ a b c d (gParity K Γ (a + b) c d)
    φ₄.toLinearMap (canon_hφ₄ K Γ a b c d) (gParity K Γ a b (c + d)) φ₅.toLinearMap
    (canon_hφ₅ K Γ a b c d) hbotbij
  have hbotmem := gBotRoute_mem K Γ a b c d (gParity K Γ (a + b) c d) φ₄.toLinearMap
      (canon_hφ₄ K Γ a b c d) (gParity K Γ a b (c + d)) φ₅.toLinearMap (canon_hφ₅ K Γ a b c d)
    (gTCanon_mem_gInterSpace K Γ (a + b) c d) (gTCanon_mem_gInterSpace K Γ a b (c + d))
  have htopmemG := (mem_gQuadInterSpace_iff_gradedHomF K Γ a b c d).mp htopmem
  have hbotmemG := (mem_gQuadInterSpace_iff_gradedHomF K Γ a b c d).mp hbotmem
  haveI := gbl_finite K Γ a b c
  haveI := gbr_finite K Γ a b c
  haveI : Module.Finite K (GQ4 K Γ a b c d) :=
    Module.Finite.equiv (LinearEquiv.ofBijective
      (gBotRoute K Γ a b c d (gParity K Γ (a + b) c d) φ₄.toLinearMap (canon_hφ₄ K Γ a b c d)
        (gParity K Γ a b (c + d)) φ₅.toLinearMap (canon_hφ₅ K Γ a b c d)) hbotbij)
  have hle := gradedHomF_finrank_sum_le_one
    (ℳ := GQ1.grading K Γ a b c d) (𝒯 := gQuadEnvGrading K Γ a b c d)
    (𝒩 := GQ4.grading K Γ a b c d)
    (gQuadEnvSplit K Γ a b c d) (gQuadEnvSize_ne_zero K Γ a b c d)
    (finrank_GQ1_eq_gQuadEnvSize K Γ a b c d)
    (finrank_GQ4_eq_gQuadEnvSize K Γ a b c d φ₄.toLinearMap (canon_hφ₄ K Γ a b c d) φ₅.toLinearMap
      (canon_hφ₅ K Γ a b c d) hbotbij)
  by_contra hne
  have hd1 : gParity K Γ (a + b) c d + gParity K Γ a b (c + d)
      = (gParity K Γ a b c + gParity K Γ a (b + c) d + gParity K Γ b c d) + 1 := by
    rcases zmod2_cases (gParity K Γ (a + b) c d + gParity K Γ a b (c + d)) with h0 | h1
    · rcases zmod2_cases (gParity K Γ a b c + gParity K Γ a (b + c) d + gParity K Γ b c d) with
        h0' | h1'
      · exact absurd (h0.trans h0'.symm) (Ne.symm hne)
      · rw [h0, h1']; decide
    · rcases zmod2_cases (gParity K Γ a b c + gParity K Γ a (b + c) d + gParity K Γ b c d) with
        h0' | h1'
      · rw [h1, h0']; decide
      · exact absurd (h1.trans h1'.symm) (Ne.symm hne)
  have htopmemG' :
      gradedHomF (GQ1.grading K Γ a b c d) (gQuadEnvGrading K Γ a b c d) (GQ4.grading K Γ a b c d)
          (gParity K Γ a b c + gParity K Γ a (b + c) d + gParity K Γ b c d) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).mpr ⟨_, htopmemG, htopne⟩
  obtain ⟨hbot0, -, -⟩ := parityConcentration (GQ1.grading K Γ a b c d) (gQuadEnvGrading K Γ a b c d)
    (𝒩 := GQ4.grading K Γ a b c d) hle htopmemG'
  rw [hd1, hbot0] at hbotmemG
  exact hbotne (Submodule.mem_bot _ |>.mp hbotmemG)

/-! ### `gChiCanon`: THE paper's `χ`, canonically -/

/-- `gTopRoute`'s membership at the canonical data, converted (via
`gParity_cocycle`) to the common degree `gBotRoute`'s own canonical data
lands at. -/
private theorem gChiCanon_htop :
    gTopRoute K Γ a b c d (gTCanon K Γ a b c).toLinearMap (canon_right K Γ a b c)
        (gParity K Γ a (b + c) d) (gt2Canon K Γ a b c d (gTCanon K Γ a (b + c) d)).toLinearMap
        (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
          (gTCanon_mem_gInterSpace K Γ a (b + c) d))
        (gTCanon K Γ b c d).toLinearMap (canon_right K Γ b c d)
      ∈ gQuadInterSpace K Γ a b c d (gParity K Γ (a + b) c d + gParity K Γ a b (c + d)) :=
  gParity_cocycle K Γ a b c d ▸
    gTopRoute_mem K Γ a b c d (gTCanon K Γ a b c).toLinearMap (canon_right K Γ a b c)
      (gParity K Γ a (b + c) d) (gt2Canon K Γ a b c d (gTCanon K Γ a (b + c) d)).toLinearMap
      (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
        (gTCanon_mem_gInterSpace K Γ a (b + c) d))
      (gTCanon K Γ b c d).toLinearMap (canon_right K Γ b c d)
      (gTCanon_mem_gInterSpace K Γ a b c)
      (gt2Canon_aSlot K Γ (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
        (gTCanon_mem_gInterSpace K Γ a (b + c) d))
      (gt2Canon_dSlot K Γ (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
        (gTCanon_mem_gInterSpace K Γ a (b + c) d))
      (gt2Canon_rightSlot K Γ (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
        (gTCanon_mem_gInterSpace K Γ a (b + c) d))
      (gt2Canon_mem_grading K Γ (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
        (gTCanon_mem_gInterSpace K Γ a (b + c) d))
      (gTCanon_mem_gInterSpace K Γ b c d)

/-- The spanning hypothesis at the canonical bottom-route data
(`gHspan`). -/
private theorem gChiCanon_hspan :
    ∀ f ∈ gQuadInterSpace K Γ a b c d (gParity K Γ (a + b) c d + gParity K Γ a b (c + d)),
      ∃ cc : K, f = cc • gBotRoute K Γ a b c d (gParity K Γ (a + b) c d)
        (gTCanon K Γ (a + b) c d).toLinearMap (canon_hφ₄ K Γ a b c d)
        (gParity K Γ a b (c + d)) (gTCanon K Γ a b (c + d)).toLinearMap (canon_hφ₅ K Γ a b c d) :=
  gHspan K Γ a b c d (gTCanon K Γ (a + b) c d) (gTCanon_mem_gInterSpace K Γ (a + b) c d)
    (gTCanon K Γ a b (c + d)) (gTCanon_mem_gInterSpace K Γ a b (c + d))

/-- **`gChiCanon Γ a b c d`**: `gChi` instantiated at the canonical
Skolem–Noether-free data — `gTCanon` at the four literal triples `(a,b,c)`,
`(b,c,d)`, `(a+b,c,d)`, `(a,b,c+d)`, and `gt2Canon (gTCanon Γ a (b+c) d)`
at the recast triple `(a,b+c,d)`; the common-degree hypothesis discharged
by `gParity_cocycle`.  THE paper's `χ`, defined canonically from bimodule
isomorphism data over any division fusion gauge `Γ` — no Skolem–Noether,
no matrix frames; unique up to the intertwiner normalizations (a
coboundary). -/
noncomputable def gChiCanon : K :=
  gChi K Γ a b c d
    (gTCanon K Γ a b c).toLinearMap (canon_right K Γ a b c)
    (gParity K Γ a (b + c) d) (gt2Canon K Γ a b c d (gTCanon K Γ a (b + c) d)).toLinearMap
    (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
      (gTCanon_mem_gInterSpace K Γ a (b + c) d))
    (gTCanon K Γ b c d).toLinearMap (canon_right K Γ b c d)
    (gParity K Γ (a + b) c d) (gTCanon K Γ (a + b) c d).toLinearMap (canon_hφ₄ K Γ a b c d)
    (gParity K Γ a b (c + d)) (gTCanon K Γ a b (c + d)).toLinearMap (canon_hφ₅ K Γ a b c d)
    (gChiCanon_htop K Γ a b c d) (gChiCanon_hspan K Γ a b c d)

/-- **`gChiCanon_spec`**: the defining pentagon equation, at the canonical
data — a direct instantiation of `gChi_spec`. -/
theorem gChiCanon_spec :
    gTopRoute K Γ a b c d (gTCanon K Γ a b c).toLinearMap (canon_right K Γ a b c)
        (gParity K Γ a (b + c) d) (gt2Canon K Γ a b c d (gTCanon K Γ a (b + c) d)).toLinearMap
        (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
          (gTCanon_mem_gInterSpace K Γ a (b + c) d))
        (gTCanon K Γ b c d).toLinearMap (canon_right K Γ b c d)
      = gChiCanon K Γ a b c d
          • gBotRoute K Γ a b c d (gParity K Γ (a + b) c d) (gTCanon K Γ (a + b) c d).toLinearMap
              (canon_hφ₄ K Γ a b c d)
              (gParity K Γ a b (c + d)) (gTCanon K Γ a b (c + d)).toLinearMap
              (canon_hφ₅ K Γ a b c d) :=
  gChi_spec K Γ a b c d (gTCanon K Γ a b c).toLinearMap (canon_right K Γ a b c)
    (gParity K Γ a (b + c) d) (gt2Canon K Γ a b c d (gTCanon K Γ a (b + c) d)).toLinearMap
    (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
      (gTCanon_mem_gInterSpace K Γ a (b + c) d))
    (gTCanon K Γ b c d).toLinearMap (canon_right K Γ b c d)
    (gParity K Γ (a + b) c d) (gTCanon K Γ (a + b) c d).toLinearMap (canon_hφ₄ K Γ a b c d)
    (gParity K Γ a b (c + d)) (gTCanon K Γ a b (c + d)).toLinearMap (canon_hφ₅ K Γ a b c d)
    (gChiCanon_htop K Γ a b c d) (gChiCanon_hspan K Γ a b c d)

/-- **`gChiCanon_ne_zero`**: `gChiCanon ≠ 0` — a direct instantiation of
`gChi_ne_zero`, using the canonical top route's own bijectivity. -/
theorem gChiCanon_ne_zero : gChiCanon K Γ a b c d ≠ 0 := by
  haveI := gq1_finite K Γ a b c d
  haveI := gq1_nontrivial K Γ a b c d
  have hφ₂equiv := gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) d)
    (gParity K Γ a (b + c) d) (gTCanon_mem_gInterSpace K Γ a (b + c) d)
  have htopbij : Function.Bijective
      (gTopRoute K Γ a b c d (gTCanon K Γ a b c).toLinearMap (canon_right K Γ a b c)
        (gParity K Γ a (b + c) d) (gt2Canon K Γ a b c d (gTCanon K Γ a (b + c) d)).toLinearMap
        hφ₂equiv (gTCanon K Γ b c d).toLinearMap (canon_right K Γ b c d)) :=
    gTopRoute_bijective K Γ a b c d (gTCanon K Γ a b c) (canon_right K Γ a b c)
      (gParity K Γ a (b + c) d) (gt2Canon K Γ a b c d (gTCanon K Γ a (b + c) d)) hφ₂equiv
      (gTCanon K Γ b c d) (canon_right K Γ b c d)
  exact gChi_ne_zero K Γ a b c d (gTCanon K Γ a b c).toLinearMap (canon_right K Γ a b c)
    (gParity K Γ a (b + c) d) (gt2Canon K Γ a b c d (gTCanon K Γ a (b + c) d)).toLinearMap
    hφ₂equiv (gTCanon K Γ b c d).toLinearMap (canon_right K Γ b c d)
    (gParity K Γ (a + b) c d) (gTCanon K Γ (a + b) c d).toLinearMap (canon_hφ₄ K Γ a b c d)
    (gParity K Γ a b (c + d)) (gTCanon K Γ a b (c + d)).toLinearMap (canon_hφ₅ K Γ a b c d)
    (gChiCanon_htop K Γ a b c d) (gChiCanon_hspan K Γ a b c d)
    (gTopRoute_ne_zero_of_bijective K Γ a b c d (gTCanon K Γ a b c).toLinearMap
      (canon_right K Γ a b c) (gParity K Γ a (b + c) d)
      (gt2Canon K Γ a b c d (gTCanon K Γ a (b + c) d)).toLinearMap hφ₂equiv
      (gTCanon K Γ b c d).toLinearMap (canon_right K Γ b c d) htopbij)

end GaugeChi

end Superfusion
