/-
Superfusion / GaugeChi / QuintEdges2

Milestone M13-2′ of the abstract `(p, χ)` arc: **six more of the 21
quintuple edge maps** (`docs/m13-design.md`), continuing `GaugeChi.QuintEdges`
(8 of 21 landed there) with the three scoped "non-cluster" genres:

* `E2M`, `E7M` (`GE2`-style): built on `gq2Assoc_rightTotal`.
* `E5M`, `E10M` (`GE5`+`gq4Close`-composite): built on `gq5Swap_rightTotal`
  and `gq4Close_rightTotal`.
* `E13M`, `E15M` (four-letter recast genre): built on a `FourLetterRecast`-
  style device one level up from `gq2rCast`.
-/
import Superfusion.GaugeChi.QuintEdges

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

/-! ### Toolkit piece 8: `gq2Assoc`'s `Total`-naturality -/

/-- **The `(b+c)`-slot vs. `D_{a+b+c+d}`-recast commutation on `GQ2rInner`**
(needed for `rightActionEnd` to typecheck against `GQ2rInner K Γ a b c d`
directly): the Γ-mirror of `Quint.lean`'s `instSMulCommClassGQ3InnerRecast4`,
one level shallower (`GQ2rInner`'s first factor is a plain `FusionColumn`,
not a further `RelTensor`) — the same `leftActionEnd_comm_rightActionEnd`
source fact. -/
instance instSMulCommClassGQ2rInnerTotal :
    SMulCommClass (Γ.D (b + c)).carrier ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ
      (GQ2rInner K Γ a b c d) := by
  refine ⟨fun y t w => ?_⟩
  show (leftActionEnd K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
        (FusionColumn (Γ.fuse (a + b + c) d)) y)
      ((rightActionEnd K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
          (FusionColumn (Γ.fuse (a + b + c) d)) t) w)
    = (rightActionEnd K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
          (FusionColumn (Γ.fuse (a + b + c) d)) t)
        ((leftActionEnd K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
          (FusionColumn (Γ.fuse (a + b + c) d)) y) w)
  rw [← Module.End.mul_apply, ← Module.End.mul_apply,
    leftActionEnd_comm_rightActionEnd K (Γ.D (a + b + c)).carrier
      (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d))]

instance instIsScalarTowerGQ2rInnerTotal :
    IsScalarTower K ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ (GQ2rInner K Γ a b c d) := by
  refine ⟨fun k t w => ?_⟩
  show (rightActionEnd K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
      (FusionColumn (Γ.fuse (a + b + c) d)) (k • t)) w
    = k • (rightActionEnd K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
        (FusionColumn (Γ.fuse (a + b + c) d)) t) w
  rw [map_smul, LinearMap.smul_apply]

theorem gq2Assoc_rightTotal (a b c d : G) (τ : (Γ.D (a + b + c + d)).carrier)
    (m : GQ2 K Γ a b c d) :
    gq2Assoc K Γ a b c d (MulOpposite.op τ • m)
      = rightActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
          (GQ2rInner K Γ a b c d) (MulOpposite.op τ) (gq2Assoc K Γ a b c d m) := by
  rw [GQ2Total_op_smul_def]
  induction m using RelTensor.induction_on with
  | zero =>
      calc gq2Assoc K Γ a b c d
            (rightActionEnd K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
              (FusionColumn (Γ.fuse (a + b + c) d)) (MulOpposite.op τ) 0)
          = gq2Assoc K Γ a b c d 0 := congrArg (gq2Assoc K Γ a b c d) (map_zero _)
        _ = 0 := map_zero _
        _ = rightActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
              (GQ2rInner K Γ a b c d) (MulOpposite.op τ) 0 := (map_zero _).symm
        _ = rightActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
              (GQ2rInner K Γ a b c d) (MulOpposite.op τ) (gq2Assoc K Γ a b c d 0) :=
            congrArg _ (map_zero _).symm
  | mk u v =>
      rw [rightActionEnd_mk]
      induction u using RelTensor.induction_on with
      | zero =>
          have e0 : RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
                (FusionColumn (Γ.fuse (a + b + c) d)) (0 : GBR Γ a b c) (MulOpposite.op τ • v)
              = (0 : GQ2 K Γ a b c d) :=
            (LinearMap.congr_fun (map_zero (RelTensor.mk K (Γ.D (a + b + c)).carrier
              (GBR Γ a b c) (FusionColumn (Γ.fuse (a + b + c) d)))) (MulOpposite.op τ • v)).trans
              (LinearMap.zero_apply _)
          have e0' : RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
                (FusionColumn (Γ.fuse (a + b + c) d)) (0 : GBR Γ a b c) v
              = (0 : GQ2 K Γ a b c d) :=
            (LinearMap.congr_fun (map_zero (RelTensor.mk K (Γ.D (a + b + c)).carrier
              (GBR Γ a b c) (FusionColumn (Γ.fuse (a + b + c) d)))) v).trans
              (LinearMap.zero_apply _)
          calc gq2Assoc K Γ a b c d (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
                (FusionColumn (Γ.fuse (a + b + c) d)) (0 : GBR Γ a b c) (MulOpposite.op τ • v))
              = gq2Assoc K Γ a b c d 0 := congrArg (gq2Assoc K Γ a b c d) e0
            _ = 0 := map_zero _
            _ = rightActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
                  (GQ2rInner K Γ a b c d) (MulOpposite.op τ) 0 := (map_zero _).symm
            _ = rightActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
                  (GQ2rInner K Γ a b c d) (MulOpposite.op τ)
                  (gq2Assoc K Γ a b c d (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
                    (FusionColumn (Γ.fuse (a + b + c) d)) (0 : GBR Γ a b c) v)) :=
                congrArg _ (congrArg (gq2Assoc K Γ a b c d) e0').symm
      | mk u' v' =>
          show gq2Assoc K Γ a b c d (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
              (FusionColumn (Γ.fuse (a + b + c) d)) (GBR.mk Γ a b c u' v') (MulOpposite.op τ • v))
            = rightActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
                (GQ2rInner K Γ a b c d) (MulOpposite.op τ)
                (gq2Assoc K Γ a b c d (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
                  (FusionColumn (Γ.fuse (a + b + c) d)) (GBR.mk Γ a b c u' v') v))
          rw [gq2Assoc_mk, gq2Assoc_mk, rightActionEnd_mk]
          exact congrArg _ (rightActionEnd_mk K (Γ.D (a + b + c)).carrier
            (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d))
            (MulOpposite.op τ) v' v).symm
      | add x y hx hy =>
          have e1 := LinearMap.map_add₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
            (FusionColumn (Γ.fuse (a + b + c) d))) x y (MulOpposite.op τ • v)
          have e2 := LinearMap.map_add₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
            (FusionColumn (Γ.fuse (a + b + c) d))) x y v
          calc gq2Assoc K Γ a b c d (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
                (FusionColumn (Γ.fuse (a + b + c) d)) (x + y) (MulOpposite.op τ • v))
              = gq2Assoc K Γ a b c d
                  (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
                      (FusionColumn (Γ.fuse (a + b + c) d)) x (MulOpposite.op τ • v)
                    + RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
                      (FusionColumn (Γ.fuse (a + b + c) d)) y (MulOpposite.op τ • v)) :=
                congrArg (gq2Assoc K Γ a b c d) e1
            _ = gq2Assoc K Γ a b c d (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
                    (FusionColumn (Γ.fuse (a + b + c) d)) x (MulOpposite.op τ • v))
                + gq2Assoc K Γ a b c d (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
                    (FusionColumn (Γ.fuse (a + b + c) d)) y (MulOpposite.op τ • v)) := map_add _ _ _
            _ = rightActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
                  (GQ2rInner K Γ a b c d) (MulOpposite.op τ)
                  (gq2Assoc K Γ a b c d (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
                    (FusionColumn (Γ.fuse (a + b + c) d)) x v))
                + rightActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
                  (GQ2rInner K Γ a b c d) (MulOpposite.op τ)
                  (gq2Assoc K Γ a b c d (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
                    (FusionColumn (Γ.fuse (a + b + c) d)) y v)) := congrArg₂ (· + ·) hx hy
            _ = rightActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
                  (GQ2rInner K Γ a b c d) (MulOpposite.op τ)
                  (gq2Assoc K Γ a b c d (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
                      (FusionColumn (Γ.fuse (a + b + c) d)) x v)
                    + gq2Assoc K Γ a b c d (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
                      (FusionColumn (Γ.fuse (a + b + c) d)) y v)) := (map_add _ _ _).symm
            _ = rightActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
                  (GQ2rInner K Γ a b c d) (MulOpposite.op τ)
                  (gq2Assoc K Γ a b c d (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
                    (FusionColumn (Γ.fuse (a + b + c) d)) (x + y) v)) :=
                congrArg _ (congrArg (gq2Assoc K Γ a b c d) e2).symm
  | add x y hx hy =>
      have e := map_add (rightActionEnd K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
        (FusionColumn (Γ.fuse (a + b + c) d)) (MulOpposite.op τ)) x y
      calc gq2Assoc K Γ a b c d
            (rightActionEnd K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
              (FusionColumn (Γ.fuse (a + b + c) d)) (MulOpposite.op τ) (x + y))
          = gq2Assoc K Γ a b c d
              (rightActionEnd K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
                  (FusionColumn (Γ.fuse (a + b + c) d)) (MulOpposite.op τ) x
                + rightActionEnd K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
                  (FusionColumn (Γ.fuse (a + b + c) d)) (MulOpposite.op τ) y) :=
            congrArg (gq2Assoc K Γ a b c d) e
        _ = gq2Assoc K Γ a b c d (rightActionEnd K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
              (FusionColumn (Γ.fuse (a + b + c) d)) (MulOpposite.op τ) x)
            + gq2Assoc K Γ a b c d (rightActionEnd K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
              (FusionColumn (Γ.fuse (a + b + c) d)) (MulOpposite.op τ) y) := map_add _ _ _
        _ = rightActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
              (GQ2rInner K Γ a b c d) (MulOpposite.op τ) (gq2Assoc K Γ a b c d x)
            + rightActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
              (GQ2rInner K Γ a b c d) (MulOpposite.op τ) (gq2Assoc K Γ a b c d y) := congrArg₂ (· + ·) hx hy
        _ = rightActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
              (GQ2rInner K Γ a b c d) (MulOpposite.op τ)
              (gq2Assoc K Γ a b c d x + gq2Assoc K Γ a b c d y) := (map_add _ _ _).symm
        _ = rightActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
              (GQ2rInner K Γ a b c d) (MulOpposite.op τ) (gq2Assoc K Γ a b c d (x + y)) :=
            congrArg _ (map_add _ _ _).symm

/-! ### Toolkit piece 9: the natural/recast bridge on `GQ3Inner`'s two
`D_{a+b+c+d}`-flavoured Total actions -/

/-- `GQ3Inner`'s NATURAL (`PentagonActions.lean`, `D_{a+(b+c+d)}`) Total
action, `rfl`-bridged to the raw `rightActionEnd` on its own two factors —
the natural-instance mirror of `GQ3InnerTotal_op_smul_def` (which bridges the
RECAST `D_{a+b+c+d}` action instead). -/
theorem GQ3InnerNatural_op_smul_def (σ : (Γ.D (a + (b + c + d))).carrier)
    (n : GQ3Inner K Γ a b c d) :
    MulOpposite.op σ • n
      = rightActionEnd K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse (b + c) d))
          (FusionColumn (Γ.fuse a (b + c + d))) (MulOpposite.op σ) n := rfl

/-- **The raw computation behind `GQ3Inner`'s natural/recast agreement**:
`rightActionEnd` on `GQ3Inner`'s own two factors, evaluated at the CAST
coefficient vs. the RECAST coefficient, agree — via `rightActionEnd_mk`'s
`map_zero`/`map_add`/mk-case induction (never touching a `def`-wrapped
smul mid-proof, per the file's discipline). -/
theorem GQ3Inner_natural_recast_smul_eq (τ : (Γ.D (a + b + c + d)).carrier)
    (n : GQ3Inner K Γ a b c d) :
    rightActionEnd K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse (b + c) d))
        (FusionColumn (Γ.fuse a (b + c + d)))
        (MulOpposite.op ((Γ.gaugeCast (add_assoc_four a b c d)).toAlgEquiv τ)) n
      = rightActionEnd K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse (b + c) d))
          (FusionColumn (Γ.fuse a (b + c + d))) (MulOpposite.op τ) n := by
  induction n using RelTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | mk v w => rw [rightActionEnd_mk, rightActionEnd_mk, fusionColumnRecast4_op_smul_def]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **`GQ3Inner`'s natural and recast Total actions AGREE** (pointwise,
registered `•` on both sides): the `.trans`-composite of
`GQ3InnerNatural_op_smul_def`, `GQ3Inner_natural_recast_smul_eq`, and
`GQ3InnerTotal_op_smul_def` (symm) — a pure term, no mid-proof `rw` against
a `def`-wrapped smul. -/
theorem GQ3Inner_natural_recast_eq (τ : (Γ.D (a + b + c + d)).carrier) (n : GQ3Inner K Γ a b c d) :
    MulOpposite.op ((Γ.gaugeCast (add_assoc_four a b c d)).toAlgEquiv τ) • n
      = MulOpposite.op τ • n :=
  (GQ3InnerNatural_op_smul_def K Γ a b c d _ n).trans
    ((GQ3Inner_natural_recast_smul_eq K Γ a b c d τ n).trans
      (GQ3InnerTotal_op_smul_def K Γ a b c d τ n).symm)

/-! ### Toolkit piece 10: `GE2`'s `Total`-equivariance -/

/-- **`gt2Canon`'s `Total`-equivariance, generalized off the generators**
(the `n`-generalization of `gt2Canon_rightSlot`, extending the mk-level fact
to every `n : GQ2rInner K Γ a b c d` by linearity, landing in `GQ3Inner`'s
RECAST `D_{a+b+c+d}` action via `GQ3Inner_natural_recast_eq`). -/
theorem gt2Canon_rightSlot_general (φ : GBL Γ a (b + c) d ≃ₗ[K] GBR Γ a (b + c) d) (e : ZMod 2)
    (hφ : φ.toLinearMap ∈ gInterSpace K Γ a (b + c) d e) (τ : (Γ.D (a + b + c + d)).carrier)
    (n : GQ2rInner K Γ a b c d) :
    gt2Canon K Γ a b c d φ (MulOpposite.op τ • n)
      = MulOpposite.op τ • gt2Canon K Γ a b c d φ n := by
  induction n using RelTensor.induction_on with
  | zero =>
      calc gt2Canon K Γ a b c d φ (MulOpposite.op τ • (0 : GQ2rInner K Γ a b c d))
          = gt2Canon K Γ a b c d φ 0 := congrArg _ (smul_zero _)
        _ = 0 := map_zero _
        _ = MulOpposite.op τ • (0 : GQ3Inner K Γ a b c d) := (smul_zero _).symm
        _ = MulOpposite.op τ • gt2Canon K Γ a b c d φ 0 := congrArg _ (map_zero _).symm
  | mk v w =>
      exact (gt2Canon_rightSlot K Γ φ e hφ τ v w).trans (GQ3Inner_natural_recast_eq K Γ a b c d τ _)
  | add x y hx hy =>
      calc gt2Canon K Γ a b c d φ (MulOpposite.op τ • (x + y))
          = gt2Canon K Γ a b c d φ (MulOpposite.op τ • x + MulOpposite.op τ • y) :=
            congrArg _ (smul_add _ _ _)
        _ = gt2Canon K Γ a b c d φ (MulOpposite.op τ • x)
            + gt2Canon K Γ a b c d φ (MulOpposite.op τ • y) := map_add _ _ _
        _ = MulOpposite.op τ • gt2Canon K Γ a b c d φ x
            + MulOpposite.op τ • gt2Canon K Γ a b c d φ y := congrArg₂ (· + ·) hx hy
        _ = MulOpposite.op τ • (gt2Canon K Γ a b c d φ x + gt2Canon K Γ a b c d φ y) :=
            (smul_add _ _ _).symm
        _ = MulOpposite.op τ • gt2Canon K Γ a b c d φ (x + y) :=
            congrArg _ (map_add _ _ _).symm

/-- **`GE2`'s `Total`-equivariance**, at the FIXED `gTCanon`/`gt2Canon`
generator, at `(a,b,c,d)` — reused VERBATIM (mirror image) at `(b,c,d,e)`
for edge 7. -/
theorem GE2_rightTotal (a b c d : G) (τ : (Γ.D (a + b + c + d)).carrier)
    (m : GQ2 K Γ a b c d) :
    GE2 K Γ a b c d (gParity K Γ a (b + c) d)
        (gt2Canon K Γ a b c d (gTCanon K Γ a (b + c) d)).toLinearMap
        (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
          (gTCanon_mem_gInterSpace K Γ a (b + c) d)) (MulOpposite.op τ • m)
      = MulOpposite.op τ •
          GE2 K Γ a b c d (gParity K Γ a (b + c) d)
            (gt2Canon K Γ a b c d (gTCanon K Γ a (b + c) d)).toLinearMap
            (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
              (gTCanon_mem_gInterSpace K Γ a (b + c) d)) m := by
  rw [GQ3Total_op_smul_def]
  show (smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
        (gt2Canon K Γ a b c d (gTCanon K Γ a (b + c) d)).toLinearMap (gParity K Γ a (b + c) d)
        (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
          (gTCanon_mem_gInterSpace K Γ a (b + c) d)))
      (gq2Assoc K Γ a b c d (MulOpposite.op τ • m))
    = rightActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ3Inner K Γ a b c d)
        (MulOpposite.op τ)
        ((smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
            (gt2Canon K Γ a b c d (gTCanon K Γ a (b + c) d)).toLinearMap (gParity K Γ a (b + c) d)
            (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
              (gTCanon_mem_gInterSpace K Γ a (b + c) d))) (gq2Assoc K Γ a b c d m))
  rw [gq2Assoc_rightTotal]
  exact LinearMap.congr_fun
    (smap_comp_rightActionEnd (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
      (gt2Canon K Γ a b c d (gTCanon K Γ a (b + c) d)).toLinearMap (gParity K Γ a (b + c) d)
      (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
        (gTCanon_mem_gInterSpace K Γ a (b + c) d))
      (gt2Canon_rightSlot_general K Γ a b c d (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
        (gTCanon_mem_gInterSpace K Γ a (b + c) d) τ))
    (gq2Assoc K Γ a b c d m)

/-! ### Toolkit piece 11: `GBL Γ a b (c+d)`'s `D_{a+b+c+d}` recast (the
`gq5Swap`-target's coefficient) -/

/-- **The `D_{a+b+c+d}` recast right action on `GBL Γ a b (c+d)`**: pulled
back, along `Γ.gaugeCast (add_assoc (a+b) c d) : a+b+c+d = (a+b)+(c+d)`,
from `GBL`'s own NATURAL total (`RouteBimod.lean`'s generic construction at
the triple `(a,b,c+d)`, whose natural coefficient is literally
`D_{a+b+(c+d)} = D_{(a+b)+(c+d)}`) — the Γ-mirror of `RouteBimod.lean`'s
`GBR`-recast device (`GBR.recast_op_smul_def`), now for `GBL`'s THIRD-slot
recast instead of `GBR`'s FIRST. Needed so that `gq5Swap`'s target `GQ5s`
(`= F_{c,d} ⊗_{D_{c+d}} GBL Γ a b (c+d)`) carries the quintuple's own
`D_{a+b+c+d}`-total. -/
noncomputable instance instModuleGBLCslotRecast :
    Module ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ (GBL Γ a b (c + d)) :=
  Module.compHom _ (((Γ.gaugeCast (add_assoc (a + b) c d)).toAlgEquiv.toRingHom).op)

theorem GBL_cslot_recast_op_smul_def (t : (Γ.D (a + b + c + d)).carrier) (w : GBL Γ a b (c + d)) :
    MulOpposite.op t • w
      = MulOpposite.op ((Γ.gaugeCast (add_assoc (a + b) c d)).toAlgEquiv t) • w := rfl

theorem GBL_cslot_recast_smul_mk (t : (Γ.D (a + b + c + d)).carrier)
    (u : FusionColumn (Γ.fuse a b)) (w : FusionColumn (Γ.fuse (a + b) (c + d))) :
    MulOpposite.op t • GBL.mk Γ a b (c + d) u w
      = GBL.mk Γ a b (c + d) u
          (MulOpposite.op ((Γ.gaugeCast (add_assoc (a + b) c d)).toAlgEquiv t) • w) := by
  rw [GBL_cslot_recast_op_smul_def, GBL.right_smul_mk]

/-- **The `(c+d)`-slot vs. `D_{a+b+c+d}`-recast commutation on `GBL Γ a b
(c+d)`**: the Γ-mirror of `Quint.lean`'s `instSMulCommClassGBRAslotRecast`,
via the SAME `midEnd_comm_rightActionEnd` source fact (`GBL`'s `(c+d)`-slot
IS a signed middle action, the direct — non-swapped — supercommutation,
`RouteBimod.lean`'s `GBL`'s own `D_c`-slot pattern). -/
instance instSMulCommClassGBLCslotRecast :
    SMulCommClass (Γ.D (c + d)).carrier ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ (GBL Γ a b (c + d)) := by
  refine ⟨fun x t w => ?_⟩
  show (midEnd (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b)) (Γ.D (c + d)).grading
        (FusionColumn.superCommSMul (Γ.fuse (a + b) (c + d))) x)
      ((rightActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (FusionColumn (Γ.fuse (a + b) (c + d)))
          (MulOpposite.op ((Γ.gaugeCast (add_assoc (a + b) c d)).toAlgEquiv
            (MulOpposite.unop t)))) w)
    = (rightActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (FusionColumn (Γ.fuse (a + b) (c + d)))
          (MulOpposite.op ((Γ.gaugeCast (add_assoc (a + b) c d)).toAlgEquiv
            (MulOpposite.unop t))))
        ((midEnd (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b)) (Γ.D (c + d)).grading
          (FusionColumn.superCommSMul (Γ.fuse (a + b) (c + d))) x) w)
  rw [← Module.End.mul_apply, ← Module.End.mul_apply,
    midEnd_comm_rightActionEnd (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
      (Γ.D (c + d)).grading (FusionColumn.superCommSMul (Γ.fuse (a + b) (c + d)))]

instance instIsScalarTowerGBLCslotRecast :
    IsScalarTower K ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ (GBL Γ a b (c + d)) := by
  refine ⟨fun k t w => ?_⟩
  show (rightActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (FusionColumn (Γ.fuse (a + b) (c + d)))
      (MulOpposite.op ((Γ.gaugeCast (add_assoc (a + b) c d)).toAlgEquiv
        (MulOpposite.unop (k • t))))) w
    = k • (rightActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (FusionColumn (Γ.fuse (a + b) (c + d)))
      (MulOpposite.op ((Γ.gaugeCast (add_assoc (a + b) c d)).toAlgEquiv (MulOpposite.unop t)))) w
  rw [MulOpposite.unop_smul, map_smul, MulOpposite.op_smul, map_smul, LinearMap.smul_apply]

/-! ### Toolkit piece 12: `gq5Swap`'s closed generator formula and
`Total`-naturality -/

/-- Public re-statement of `Pentagon.lean`'s `private gq5LawA`, needed
verbatim across the file boundary for `gq5Swap_mk_mk`. -/
theorem gq5LawA' :
    MidSignLaw K (Γ.D (a + b)).carrier (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
      (FusionColumn (Γ.fuse (a + b) (c + d)))
      (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse c d)) := by
  intro l i x hx n hn p
  exact GBR.aslot_smul_mk_of_mem (Γ := Γ) (a := a + b) (b := c) (c := d) hx hn p

/-- Public re-statement of `Pentagon.lean`'s `private gq5LawB`. -/
theorem gq5LawB' :
    MidSignLaw K (Γ.D (c + d)).carrier (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (FusionColumn (Γ.fuse (a + b) (c + d)))
      (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse a b)) := by
  intro l i z hz m hm p
  exact GBL.cslot_smul_mk_of_mem (Γ := Γ) (a := a) (b := b) (c := c + d) hz hm p

/-- **The closed (non-homogeneous) generator formula of `gq5Swap`**: the
`u,v`-generic form of `gq5Swap_mk_of_mem`, via `midSwapMap_mk_mk`'s
closed-form computation (`(-1)^{|u||v|}` expanded through the odd
projections — no degree hypothesis on `u`/`v`). -/
theorem gq5Swap_mk_mk (u : FusionColumn (Γ.fuse a b)) (v : FusionColumn (Γ.fuse c d))
    (w : FusionColumn (Γ.fuse (a + b) (c + d))) :
    gq5Swap K Γ a b c d
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u
          (GBR.mk Γ (a + b) c d v w))
      = RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ a b (c + d)) v
          (GBL.mk Γ a b (c + d) u w)
        - (2 : ℤ) • RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
            (GBL Γ a b (c + d)) (modProj (FusionColumn.grading (Γ.fuse c d)) 1 v)
            (GBL.mk Γ a b (c + d) (modProj (FusionColumn.grading (Γ.fuse a b)) 1 u) w) :=
  midSwapMap_mk_mk K (Γ.D (a + b)).carrier (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse a b))
    (FusionColumn (Γ.fuse c d)) (FusionColumn (Γ.fuse (a + b) (c + d)))
    (Γ.D (a + b)).grading (Γ.D (c + d)).grading
    (FusionColumn.grading (Γ.fuse a b)) (FusionColumn.grading (Γ.fuse c d))
    (gq5LawA' K Γ a b c d) (gq5LawB' K Γ a b c d) u v w

/-- **`gq5Swap`'s `Total`-naturality**: the swap at the `(ab)(cd)`-vertex
intertwines the outer `D_{a+b+c+d}`-action, acting through the LAST tensor
factor `w` on both sides — PLAIN (no extra sign): the swap's own sign is
keyed only to `u`,`v`'s parities (`gq5Swap_mk_mk`'s closed form), and `w`'s
outer action passes straight through both `mk`-summands via
`rightActionEnd_mk`. -/
theorem gq5Swap_rightTotal (a b c d : G) (τ : (Γ.D (a + b + c + d)).carrier)
    (m : GQ5 K Γ a b c d) :
    gq5Swap K Γ a b c d (MulOpposite.op τ • m)
      = rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
          (GBL Γ a b (c + d)) (MulOpposite.op τ) (gq5Swap K Γ a b c d m) := by
  rw [GQ5Total_op_smul_def]
  induction m using RelTensor.induction_on with
  | zero =>
      calc gq5Swap K Γ a b c d
            (rightActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
              (GBR Γ (a + b) c d) (MulOpposite.op τ) 0)
          = gq5Swap K Γ a b c d 0 := congrArg (gq5Swap K Γ a b c d) (map_zero _)
        _ = 0 := map_zero _
        _ = rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
              (GBL Γ a b (c + d)) (MulOpposite.op τ) 0 := (map_zero _).symm
        _ = rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
              (GBL Γ a b (c + d)) (MulOpposite.op τ) (gq5Swap K Γ a b c d 0) :=
            congrArg _ (map_zero _).symm
  | mk u v =>
      induction v using RelTensor.induction_on with
      | zero =>
          calc gq5Swap K Γ a b c d
                (rightActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                  (GBR Γ (a + b) c d) (MulOpposite.op τ) (RelTensor.mk K (Γ.D (a + b)).carrier
                    (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u (0 : GBR Γ (a + b) c d)))
              = gq5Swap K Γ a b c d (RelTensor.mk K (Γ.D (a + b)).carrier
                  (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u
                  (MulOpposite.op τ • (0 : GBR Γ (a + b) c d))) :=
                congrArg (gq5Swap K Γ a b c d) (rightActionEnd_mk K (Γ.D (a + b)).carrier
                  (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) (MulOpposite.op τ) u 0)
            _ = gq5Swap K Γ a b c d (RelTensor.mk K (Γ.D (a + b)).carrier
                  (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u 0) :=
                congrArg (fun z => gq5Swap K Γ a b c d
                  (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                    (GBR Γ (a + b) c d) u z)) (smul_zero _)
            _ = gq5Swap K Γ a b c d 0 :=
                congrArg (gq5Swap K Γ a b c d) (map_zero
                  (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                    (GBR Γ (a + b) c d) u))
            _ = 0 := map_zero _
            _ = rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                  (GBL Γ a b (c + d)) (MulOpposite.op τ) 0 := (map_zero _).symm
            _ = rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                  (GBL Γ a b (c + d)) (MulOpposite.op τ)
                  (gq5Swap K Γ a b c d (RelTensor.mk K (Γ.D (a + b)).carrier
                    (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u 0)) :=
                congrArg _ (congrArg (gq5Swap K Γ a b c d) (map_zero
                  (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                    (GBR Γ (a + b) c d) u))).symm
      | mk v' w' =>
          have hcast : GBL.mk Γ a b (c + d) u
                (MulOpposite.op ((Γ.gaugeCast (add_assoc (a + b) c d)).toAlgEquiv τ) • w')
              = MulOpposite.op τ • GBL.mk Γ a b (c + d) u w' :=
            (GBL_cslot_recast_smul_mk K Γ a b c d τ u w').symm
          have hcast' : GBL.mk Γ a b (c + d) (modProj (FusionColumn.grading (Γ.fuse a b)) 1 u)
                (MulOpposite.op ((Γ.gaugeCast (add_assoc (a + b) c d)).toAlgEquiv τ) • w')
              = MulOpposite.op τ • GBL.mk Γ a b (c + d)
                  (modProj (FusionColumn.grading (Γ.fuse a b)) 1 u) w' :=
            (GBL_cslot_recast_smul_mk K Γ a b c d τ
              (modProj (FusionColumn.grading (Γ.fuse a b)) 1 u) w').symm
          calc gq5Swap K Γ a b c d
                (rightActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                  (GBR Γ (a + b) c d) (MulOpposite.op τ) (RelTensor.mk K (Γ.D (a + b)).carrier
                    (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u (GBR.mk Γ (a + b) c d v' w')))
              = gq5Swap K Γ a b c d (RelTensor.mk K (Γ.D (a + b)).carrier
                  (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u
                  (MulOpposite.op τ • GBR.mk Γ (a + b) c d v' w')) :=
                congrArg (gq5Swap K Γ a b c d) (rightActionEnd_mk K (Γ.D (a + b)).carrier
                  (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) (MulOpposite.op τ) u
                  (GBR.mk Γ (a + b) c d v' w'))
            _ = gq5Swap K Γ a b c d (RelTensor.mk K (Γ.D (a + b)).carrier
                  (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u
                  (GBR.mk Γ (a + b) c d v'
                    (MulOpposite.op ((Γ.gaugeCast (add_assoc (a + b) c d)).toAlgEquiv τ) • w'))) :=
                congrArg (fun z => gq5Swap K Γ a b c d
                  (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                    (GBR Γ (a + b) c d) u z))
                  (GBR.recast_smul_mk Γ (a + b) c d τ v' w')
            _ = RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ a b (c + d)) v'
                  (GBL.mk Γ a b (c + d) u
                    (MulOpposite.op ((Γ.gaugeCast (add_assoc (a + b) c d)).toAlgEquiv τ) • w'))
                - (2 : ℤ) • RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                    (GBL Γ a b (c + d)) (modProj (FusionColumn.grading (Γ.fuse c d)) 1 v')
                    (GBL.mk Γ a b (c + d) (modProj (FusionColumn.grading (Γ.fuse a b)) 1 u)
                      (MulOpposite.op ((Γ.gaugeCast (add_assoc (a + b) c d)).toAlgEquiv τ) • w')) :=
                gq5Swap_mk_mk K Γ a b c d u v'
                  (MulOpposite.op ((Γ.gaugeCast (add_assoc (a + b) c d)).toAlgEquiv τ) • w')
            _ = RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ a b (c + d)) v'
                  (MulOpposite.op τ • GBL.mk Γ a b (c + d) u w')
                - (2 : ℤ) • RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                    (GBL Γ a b (c + d)) (modProj (FusionColumn.grading (Γ.fuse c d)) 1 v')
                    (MulOpposite.op τ • GBL.mk Γ a b (c + d)
                      (modProj (FusionColumn.grading (Γ.fuse a b)) 1 u) w') := by rw [hcast, hcast']
            _ = rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                  (GBL Γ a b (c + d)) (MulOpposite.op τ)
                  (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                    (GBL Γ a b (c + d)) v' (GBL.mk Γ a b (c + d) u w'))
                - (2 : ℤ) • rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                    (GBL Γ a b (c + d)) (MulOpposite.op τ)
                    (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                      (GBL Γ a b (c + d)) (modProj (FusionColumn.grading (Γ.fuse c d)) 1 v')
                      (GBL.mk Γ a b (c + d) (modProj (FusionColumn.grading (Γ.fuse a b)) 1 u) w')) := by
                rw [rightActionEnd_mk, rightActionEnd_mk]
            _ = rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                  (GBL Γ a b (c + d)) (MulOpposite.op τ)
                  (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                      (GBL Γ a b (c + d)) v' (GBL.mk Γ a b (c + d) u w')
                    - (2 : ℤ) • RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                        (GBL Γ a b (c + d)) (modProj (FusionColumn.grading (Γ.fuse c d)) 1 v')
                        (GBL.mk Γ a b (c + d) (modProj (FusionColumn.grading (Γ.fuse a b)) 1 u) w')) := by
                rw [map_sub, map_zsmul]
            _ = rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                  (GBL Γ a b (c + d)) (MulOpposite.op τ)
                  (gq5Swap K Γ a b c d (RelTensor.mk K (Γ.D (a + b)).carrier
                    (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u (GBR.mk Γ (a + b) c d v' w'))) :=
                congrArg _ (gq5Swap_mk_mk K Γ a b c d u v' w').symm
      | add x y hx hy =>
          calc gq5Swap K Γ a b c d
                (rightActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                  (GBR Γ (a + b) c d) (MulOpposite.op τ) (RelTensor.mk K (Γ.D (a + b)).carrier
                    (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u (x + y)))
              = gq5Swap K Γ a b c d (RelTensor.mk K (Γ.D (a + b)).carrier
                  (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u (MulOpposite.op τ • (x + y))) :=
                congrArg (gq5Swap K Γ a b c d) (rightActionEnd_mk K (Γ.D (a + b)).carrier
                  (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) (MulOpposite.op τ) u (x + y))
            _ = gq5Swap K Γ a b c d (RelTensor.mk K (Γ.D (a + b)).carrier
                  (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u
                  (MulOpposite.op τ • x + MulOpposite.op τ • y)) :=
                congrArg (fun z => gq5Swap K Γ a b c d
                  (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                    (GBR Γ (a + b) c d) u z)) (smul_add _ _ _)
            _ = gq5Swap K Γ a b c d
                  (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                      (GBR Γ (a + b) c d) u (MulOpposite.op τ • x)
                    + RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                      (GBR Γ (a + b) c d) u (MulOpposite.op τ • y)) :=
                congrArg (gq5Swap K Γ a b c d) (map_add
                  (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                    (GBR Γ (a + b) c d) u) _ _)
            _ = gq5Swap K Γ a b c d (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                    (GBR Γ (a + b) c d) u (MulOpposite.op τ • x))
                + gq5Swap K Γ a b c d (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                    (GBR Γ (a + b) c d) u (MulOpposite.op τ • y)) := map_add _ _ _
            _ = rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                  (GBL Γ a b (c + d)) (MulOpposite.op τ)
                  (gq5Swap K Γ a b c d (RelTensor.mk K (Γ.D (a + b)).carrier
                    (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u x))
                + rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                  (GBL Γ a b (c + d)) (MulOpposite.op τ)
                  (gq5Swap K Γ a b c d (RelTensor.mk K (Γ.D (a + b)).carrier
                    (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u y)) := congrArg₂ (· + ·) hx hy
            _ = rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                  (GBL Γ a b (c + d)) (MulOpposite.op τ)
                  (gq5Swap K Γ a b c d (RelTensor.mk K (Γ.D (a + b)).carrier
                      (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u x)
                    + gq5Swap K Γ a b c d (RelTensor.mk K (Γ.D (a + b)).carrier
                      (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u y)) := (map_add _ _ _).symm
            _ = rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                  (GBL Γ a b (c + d)) (MulOpposite.op τ)
                  (gq5Swap K Γ a b c d (RelTensor.mk K (Γ.D (a + b)).carrier
                    (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u (x + y))) :=
                congrArg _ (congrArg (gq5Swap K Γ a b c d) (map_add
                  (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                    (GBR Γ (a + b) c d) u) x y)).symm
  | add x y hx hy =>
      have e := map_add (rightActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (GBR Γ (a + b) c d) (MulOpposite.op τ)) x y
      calc gq5Swap K Γ a b c d
            (rightActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
              (GBR Γ (a + b) c d) (MulOpposite.op τ) (x + y))
          = gq5Swap K Γ a b c d
              (rightActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                  (GBR Γ (a + b) c d) (MulOpposite.op τ) x
                + rightActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                  (GBR Γ (a + b) c d) (MulOpposite.op τ) y) :=
            congrArg (gq5Swap K Γ a b c d) e
        _ = gq5Swap K Γ a b c d (rightActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
              (GBR Γ (a + b) c d) (MulOpposite.op τ) x)
            + gq5Swap K Γ a b c d (rightActionEnd K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
              (GBR Γ (a + b) c d) (MulOpposite.op τ) y) := map_add _ _ _
        _ = rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
              (GBL Γ a b (c + d)) (MulOpposite.op τ) (gq5Swap K Γ a b c d x)
            + rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
              (GBL Γ a b (c + d)) (MulOpposite.op τ) (gq5Swap K Γ a b c d y) := congrArg₂ (· + ·) hx hy
        _ = rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
              (GBL Γ a b (c + d)) (MulOpposite.op τ)
              (gq5Swap K Γ a b c d x + gq5Swap K Γ a b c d y) := (map_add _ _ _).symm
        _ = rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
              (GBL Γ a b (c + d)) (MulOpposite.op τ) (gq5Swap K Γ a b c d (x + y)) :=
            congrArg _ (map_add _ _ _).symm

/-! ### Toolkit piece 13: `GBR Γ a b (c+d)`'s `D_{a+b+c+d}` recast (the
`GQ4r`/`GE5`-target's coefficient) -/

/-- `a+b+c+d = a+(b+(c+d))`, the composed reassociation needed to recast
`FusionColumn (Γ.fuse a (b+(c+d)))` (`GBR Γ a b (c+d)`'s own second raw
factor) directly at `D_{a+b+c+d}`. -/
theorem add_assoc_four_left (a b c d : G) : a + b + c + d = a + (b + (c + d)) :=
  (add_assoc_four a b c d).trans (congrArg (a + ·) (add_assoc b c d))

/-- **The `D_{a+b+c+d}` recast right action on `FusionColumn (Γ.fuse a
(b+(c+d)))`** — `GBR Γ a b (c+d)`'s own second raw factor — via
`add_assoc_four_left`, mirroring `Quint.lean`'s `FourLetterRecast` package
one level deeper (composed reassociation instead of a single `add_assoc`). -/
noncomputable instance instModuleFusionColumnRecastABR :
    Module ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ (FusionColumn (Γ.fuse a (b + (c + d)))) :=
  Module.compHom _ (((Γ.gaugeCast (add_assoc_four_left a b c d)).toAlgEquiv.toRingHom).op)

theorem fusionColumnRecastABR_op_smul_def (t : (Γ.D (a + b + c + d)).carrier)
    (v : FusionColumn (Γ.fuse a (b + (c + d)))) :
    MulOpposite.op t • v
      = MulOpposite.op ((Γ.gaugeCast (add_assoc_four_left a b c d)).toAlgEquiv t) • v := rfl

instance instSMulCommClassFusionColumnRecastABR :
    SMulCommClass (Γ.D (b + (c + d))).carrier ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ
      (FusionColumn (Γ.fuse a (b + (c + d)))) :=
  ⟨fun s t v => smul_comm s
    (MulOpposite.op ((Γ.gaugeCast (add_assoc_four_left a b c d)).toAlgEquiv
      (MulOpposite.unop t))) v⟩

instance instIsScalarTowerFusionColumnRecastABR :
    IsScalarTower K ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ (FusionColumn (Γ.fuse a (b + (c + d)))) :=
  ⟨fun k t v => by
    show (MulOpposite.op ((Γ.gaugeCast (add_assoc_four_left a b c d)).toAlgEquiv
        (MulOpposite.unop (k • t)))) • v
      = k • ((MulOpposite.op ((Γ.gaugeCast (add_assoc_four_left a b c d)).toAlgEquiv
          (MulOpposite.unop t))) • v)
    rw [MulOpposite.unop_smul, map_smul, MulOpposite.op_smul]
    exact smul_assoc k _ v⟩

/-- **`GBR Γ a b (c+d)`'s `D_{a+b+c+d}` Total** (needed for `GQ4r`'s own
Total and `GE5`'s naturality): `rightActionEnd` on `GBR`'s own two raw
factors, `D_{a+b+c+d}` landing directly on the second (`FusionColumn (Γ.fuse
a (b+(c+d)))`) via `instModuleFusionColumnRecastABR` — mirrors
`instModuleGQ1Total`'s recipe, one level deeper. -/
noncomputable instance instModuleGBRTotal4 :
    Module ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ (GBR Γ a b (c + d)) :=
  Module.compHom
    (RelTensor K (Γ.D (b + (c + d))).carrier (FusionColumn (Γ.fuse b (c + d)))
      (FusionColumn (Γ.fuse a (b + (c + d)))))
    ((rightActionEnd K (Γ.D (b + (c + d))).carrier (FusionColumn (Γ.fuse b (c + d)))
      (FusionColumn (Γ.fuse a (b + (c + d)))) (C := (Γ.D (a + b + c + d)).carrier)).toRingHom)

theorem GBRTotal4_op_smul_def (t : (Γ.D (a + b + c + d)).carrier) (n : GBR Γ a b (c + d)) :
    MulOpposite.op t • n
      = rightActionEnd K (Γ.D (b + (c + d))).carrier (FusionColumn (Γ.fuse b (c + d)))
          (FusionColumn (Γ.fuse a (b + (c + d)))) (MulOpposite.op t) n := rfl

/-- **The `(c+d)`-slot vs. `D_{a+b+c+d}`-recast commutation on `GBR Γ a b
(c+d)`**: the `(c+d)`-slot is DIRECT (`leftActionEnd`, `RouteBimod.lean`'s
own `z`-slot pattern for `GBR`), so `leftActionEnd_comm_rightActionEnd`
applies plainly (no sign, unlike `GBL`'s middle `(c+d)`-slot). -/
instance instSMulCommClassGBRTotal4 :
    SMulCommClass (Γ.D (c + d)).carrier ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ (GBR Γ a b (c + d)) := by
  refine ⟨fun y t w => ?_⟩
  show (leftActionEnd K (Γ.D (b + (c + d))).carrier (FusionColumn (Γ.fuse b (c + d)))
        (FusionColumn (Γ.fuse a (b + (c + d)))) y)
      ((rightActionEnd K (Γ.D (b + (c + d))).carrier (FusionColumn (Γ.fuse b (c + d)))
          (FusionColumn (Γ.fuse a (b + (c + d)))) t) w)
    = (rightActionEnd K (Γ.D (b + (c + d))).carrier (FusionColumn (Γ.fuse b (c + d)))
          (FusionColumn (Γ.fuse a (b + (c + d)))) t)
        ((leftActionEnd K (Γ.D (b + (c + d))).carrier (FusionColumn (Γ.fuse b (c + d)))
          (FusionColumn (Γ.fuse a (b + (c + d)))) y) w)
  rw [← Module.End.mul_apply, ← Module.End.mul_apply,
    leftActionEnd_comm_rightActionEnd K (Γ.D (b + (c + d))).carrier
      (FusionColumn (Γ.fuse b (c + d))) (FusionColumn (Γ.fuse a (b + (c + d))))]

instance instIsScalarTowerGBRTotal4 :
    IsScalarTower K ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ (GBR Γ a b (c + d)) := by
  refine ⟨fun k t w => ?_⟩
  show (rightActionEnd K (Γ.D (b + (c + d))).carrier (FusionColumn (Γ.fuse b (c + d)))
      (FusionColumn (Γ.fuse a (b + (c + d)))) (k • t)) w
    = k • (rightActionEnd K (Γ.D (b + (c + d))).carrier (FusionColumn (Γ.fuse b (c + d)))
        (FusionColumn (Γ.fuse a (b + (c + d)))) t) w
  rw [map_smul, LinearMap.smul_apply]

/-- The `(c+d)`-slot vs. `D_{a+b+c+d}` recast at the `mk`-generator level. -/
theorem GBRTotal4_smul_mk (t : (Γ.D (a + b + c + d)).carrier)
    (v : FusionColumn (Γ.fuse b (c + d))) (w : FusionColumn (Γ.fuse a (b + (c + d)))) :
    MulOpposite.op t • GBR.mk Γ a b (c + d) v w
      = GBR.mk Γ a b (c + d) v (MulOpposite.op t • w) := by
  rw [GBRTotal4_op_smul_def]
  exact rightActionEnd_mk K (Γ.D (b + (c + d))).carrier (FusionColumn (Γ.fuse b (c + d)))
    (FusionColumn (Γ.fuse a (b + (c + d)))) (MulOpposite.op t) v w

/-! ### Toolkit piece 14: `GE5`'s `Total`-equivariance -/

/-- Two composed `Γ.gaugeCast`s along a chain `x = y = z` collapse to the
single cast along the transitivity — the public generic version of
`ChiCanon.lean`'s private `gaugeCast_trans`. -/
theorem gaugeCast_trans' {x y z : G} (h1 : x = y) (h2 : y = z) (τ : (Γ.D x).carrier) :
    (Γ.gaugeCast h2).toAlgEquiv ((Γ.gaugeCast h1).toAlgEquiv τ)
      = (Γ.gaugeCast (h1.trans h2)).toAlgEquiv τ :=
  Γ.gaugeCast_trans_apply h1 h2 τ

/-- Two composed `Γ.gaugeCast`s along `add_assoc (a+b) c d` then
`add_assoc a b (c+d)` collapse to the single cast along
`add_assoc_four_left` — `gaugeCast_trans'` plus proof irrelevance of the
composed equality. -/
theorem gaugeCast_trans_ABR (τ : (Γ.D (a + b + c + d)).carrier) :
    (Γ.gaugeCast (add_assoc a b (c + d))).toAlgEquiv
        ((Γ.gaugeCast (add_assoc (a + b) c d)).toAlgEquiv τ)
      = (Γ.gaugeCast (add_assoc_four_left a b c d)).toAlgEquiv τ :=
  gaugeCast_trans' K Γ (add_assoc (a + b) c d) (add_assoc a b (c + d)) τ

/-- **`GBR Γ a b (c+d)`'s natural (composed-cast) and `GBRTotal4`-recast
`D_{a+b+c+d}`-flavoured Total actions AGREE, at the RAW `rightActionEnd`
level** — proved by induction on a FRESH `n`, mirroring
`GQ3Inner_natural_recast_smul_eq`: the induction is done ENTIRELY at the
raw `rightActionEnd` level (never through `•` notation on the def-wrapped
`GBR Γ a b (c+d)` mid-proof), sidestepping the def-wrapped-induction trap. -/
theorem GBR_abcd_natural_recast_smul_eq (τ : (Γ.D (a + b + c + d)).carrier) (n : GBR Γ a b (c + d)) :
    rightActionEnd K (Γ.D (b + (c + d))).carrier (FusionColumn (Γ.fuse b (c + d)))
        (FusionColumn (Γ.fuse a (b + (c + d))))
        (MulOpposite.op ((Γ.gaugeCast (add_assoc a b (c + d))).toAlgEquiv
          ((Γ.gaugeCast (add_assoc (a + b) c d)).toAlgEquiv τ))) n
      = rightActionEnd K (Γ.D (b + (c + d))).carrier (FusionColumn (Γ.fuse b (c + d)))
          (FusionColumn (Γ.fuse a (b + (c + d)))) (MulOpposite.op τ) n := by
  induction n using RelTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | mk v w =>
      rw [rightActionEnd_mk, rightActionEnd_mk, gaugeCast_trans_ABR,
        fusionColumnRecastABR_op_smul_def]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **`GBR`'s natural and `GBRTotal4`-recast Total actions AGREE**
(pointwise, registered `•` on both sides): the `.trans`-composite of the
NATURAL-instance `rfl`-unfold (`GBR.recast_op_smul_def`'s own underlying
natural smul, matched up via `GBR_abcd_natural_recast_smul_eq`) and
`GBRTotal4_op_smul_def` (symm) — a pure term. -/
theorem GBR_abcd_natural_recast_eq (τ : (Γ.D (a + b + c + d)).carrier) (n : GBR Γ a b (c + d)) :
    MulOpposite.op ((Γ.gaugeCast (add_assoc a b (c + d))).toAlgEquiv
        ((Γ.gaugeCast (add_assoc (a + b) c d)).toAlgEquiv τ)) • n
      = MulOpposite.op τ • n :=
  (GBR_abcd_natural_recast_smul_eq K Γ a b c d τ n).trans (GBRTotal4_op_smul_def K Γ a b c d τ n).symm

/-- **The bridge between `gTCanon`'s NATURAL right-recast equivariance
(`gCanonRight`, `D_{(a+b)+(c+d)}`) and `GBR`'s further `D_{a+b+c+d}`
recast** — via `GBR.recast_op_smul_def` (unfolding `gCanonRight`'s own
target smul to `GBR`'s NATURAL `D_{a+(b+(c+d))}` action) and
`GBR_abcd_natural_recast_eq` (relating that to OUR `D_{a+b+c+d}` recast) —
a pure term, no induction on the compound `gTCanon … m`. -/
theorem gTCanon_abcd_rightTotal (τ : (Γ.D (a + b + c + d)).carrier) (m : GBL Γ a b (c + d)) :
    gTCanon K Γ a b (c + d) (MulOpposite.op τ • m)
      = MulOpposite.op τ • gTCanon K Γ a b (c + d) m := by
  rw [GBL_cslot_recast_op_smul_def, gCanonRight K Γ a b (c + d),
    GBR.recast_op_smul_def, ← GBR_abcd_natural_recast_eq]

/-- **`GE5`'s `Total`-equivariance**, at the FIXED `gTCanon`-instantiated
generator, at `(a,b,c,d)` — reused VERBATIM (mirror image) at `(b,c,d,e)`
for edge 10. -/
theorem GE5_rightTotal (a b c d : G) (τ : (Γ.D (a + b + c + d)).carrier)
    (m : GQ5 K Γ a b c d) :
    GE5 K Γ a b c d (gParity K Γ a b (c + d)) (gTCanon K Γ a b (c + d)).toLinearMap
        (gCanonHphi5 K Γ a b c d) (MulOpposite.op τ • m)
      = rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d))
          (MulOpposite.op τ)
          (GE5 K Γ a b c d (gParity K Γ a b (c + d)) (gTCanon K Γ a b (c + d)).toLinearMap
            (gCanonHphi5 K Γ a b c d) m) := by
  show (smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
        (gTCanon K Γ a b (c + d)).toLinearMap (gParity K Γ a b (c + d)) (gCanonHphi5 K Γ a b c d))
      (gq5Swap K Γ a b c d (MulOpposite.op τ • m))
    = rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d))
        (MulOpposite.op τ)
        ((smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
            (gTCanon K Γ a b (c + d)).toLinearMap (gParity K Γ a b (c + d))
            (gCanonHphi5 K Γ a b c d)) (gq5Swap K Γ a b c d m))
  rw [gq5Swap_rightTotal]
  exact LinearMap.congr_fun
    (smap_comp_rightActionEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
      (gTCanon K Γ a b (c + d)).toLinearMap (gParity K Γ a b (c + d)) (gCanonHphi5 K Γ a b c d)
      (gTCanon_abcd_rightTotal K Γ a b c d τ))
    (gq5Swap K Γ a b c d m)

/-! ### Toolkit piece 15: `gq4Close`'s `Total`-naturality -/

/-- **`fusionColumnCast`'s coefficient commutation**: the Γ-mirror of
`gColumnCastFst_coeff`, on the OTHER (second-index) slot — `subst`-trivial,
mirroring `fusionColumnCast`'s own construction. -/
theorem fusionColumnCast_coeff {x y : G} (h : x = y) (a : G)
    (τ : (Γ.D (a + x)).carrier) (w : FusionColumn (Γ.fuse a x)) :
    fusionColumnCast K Γ a h (MulOpposite.op τ • w)
      = MulOpposite.op ((Γ.gaugeCast (congrArg (a + ·) h)).toAlgEquiv τ)
          • fusionColumnCast K Γ a h w := by
  subst h
  rfl

/-- **`fusionColumnCast K Γ a (add_assoc b c d).symm`'s `D_{a+b+c+d}`-recast
compatibility**: OUR two FourLetterRecast-flavoured `D_{a+b+c+d}` actions on
its source (`instModuleFusionColumnRecastABR`) and target
(`Quint.lean`'s `instModuleFusionColumnRecast4`) agree across the cast —
via `fusionColumnCast_coeff` (generic) plus `gaugeCast_trans'` collapsing
the composed cast `add_assoc_four_left.trans (congrArg (a+·) (add_assoc b c
d).symm)` to `add_assoc_four a b c d` (proof irrelevance, DEFINITIONALLY —
`add_assoc_four_left` was built as exactly this composite). -/
theorem fusionColumnCast_bcd_recast (a b c d : G) (τ : (Γ.D (a + b + c + d)).carrier)
    (w : FusionColumn (Γ.fuse a (b + (c + d)))) :
    fusionColumnCast K Γ a (add_assoc b c d).symm (MulOpposite.op τ • w)
      = MulOpposite.op τ • fusionColumnCast K Γ a (add_assoc b c d).symm w := by
  rw [fusionColumnRecastABR_op_smul_def, fusionColumnCast_coeff, fusionColumnRecast4_op_smul_def,
    gaugeCast_trans']

/-- **`gq4Close`'s `Total`-naturality**: the connector at the
`a(b(cd))`-vertex intertwines the outer `D_{a+b+c+d}`-action — the assoc
leg (`gq4lAssoc`, folded into `gq4Close_mk`'s own closed form) is
sign-free, and the recast leg's compatibility is
`fusionColumnCast_bcd_recast`. Domain expressed via the raw `rightActionEnd`
on `GQ4r`'s own two factors (mirroring `gq5Swap_rightTotal`'s discipline —
`GQ4r` is `def`-wrapped); codomain via `GQ4`'s ALREADY-REGISTERED
`Total` (`Quint.lean`'s `instModuleGQ4Total`, `GQ4Total_op_smul_def`). -/
theorem gq4Close_rightTotal (a b c d : G) (τ : (Γ.D (a + b + c + d)).carrier)
    (m : GQ4r K Γ a b c d) :
    gq4Close K Γ a b c d
        (rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d))
          (MulOpposite.op τ) m)
      = MulOpposite.op τ • gq4Close K Γ a b c d m := by
  induction m using RelTensor.induction_on with
  | zero =>
      calc gq4Close K Γ a b c d
            (rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d))
              (MulOpposite.op τ) 0)
          = gq4Close K Γ a b c d 0 := congrArg (gq4Close K Γ a b c d) (map_zero _)
        _ = 0 := map_zero _
        _ = MulOpposite.op τ • (0 : GQ4 K Γ a b c d) := (smul_zero _).symm
        _ = MulOpposite.op τ • gq4Close K Γ a b c d 0 := congrArg _ (map_zero _).symm
  | mk v u =>
      induction u using RelTensor.induction_on with
      | zero =>
          calc gq4Close K Γ a b c d
                (rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                  (GBR Γ a b (c + d)) (MulOpposite.op τ) (RelTensor.mk K (Γ.D (c + d)).carrier
                    (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) v (0 : GBR Γ a b (c + d))))
              = gq4Close K Γ a b c d (RelTensor.mk K (Γ.D (c + d)).carrier
                  (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) v
                  (MulOpposite.op τ • (0 : GBR Γ a b (c + d)))) :=
                congrArg (gq4Close K Γ a b c d) (rightActionEnd_mk K (Γ.D (c + d)).carrier
                  (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) (MulOpposite.op τ) v 0)
            _ = gq4Close K Γ a b c d (RelTensor.mk K (Γ.D (c + d)).carrier
                  (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) v 0) :=
                congrArg (fun z => gq4Close K Γ a b c d (RelTensor.mk K (Γ.D (c + d)).carrier
                  (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) v z)) (smul_zero _)
            _ = gq4Close K Γ a b c d 0 :=
                congrArg (gq4Close K Γ a b c d) (map_zero (RelTensor.mk K (Γ.D (c + d)).carrier
                  (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) v))
            _ = 0 := map_zero _
            _ = MulOpposite.op τ • (0 : GQ4 K Γ a b c d) := (smul_zero _).symm
            _ = MulOpposite.op τ • gq4Close K Γ a b c d
                  (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                    (GBR Γ a b (c + d)) v 0) :=
                congrArg _ (congrArg (gq4Close K Γ a b c d) (map_zero
                  (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                    (GBR Γ a b (c + d)) v))).symm
      | mk u' w' =>
          have step1 : gq4Close K Γ a b c d
                (rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                  (GBR Γ a b (c + d)) (MulOpposite.op τ) (RelTensor.mk K (Γ.D (c + d)).carrier
                    (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) v
                    (GBR.mk Γ a b (c + d) u' w')))
              = gq4Close K Γ a b c d (RelTensor.mk K (Γ.D (c + d)).carrier
                  (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) v
                  (GBR.mk Γ a b (c + d) u' (MulOpposite.op τ • w'))) := by
            rw [rightActionEnd_mk, GBRTotal4_smul_mk]
          have step2 : gq4Close K Γ a b c d (RelTensor.mk K (Γ.D (c + d)).carrier
                (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) v
                (GBR.mk Γ a b (c + d) u' (MulOpposite.op τ • w')))
              = RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
                  (FusionColumn (Γ.fuse a (b + c + d))) (GBR.mk Γ b c d v u')
                  (MulOpposite.op τ • fusionColumnCast K Γ a (add_assoc b c d).symm w') :=
            (gq4Close_mk K Γ a b c d v u' (MulOpposite.op τ • w')).trans
              (congrArg (fun z : FusionColumn (Γ.fuse a (b + c + d)) =>
                  RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
                    (FusionColumn (Γ.fuse a (b + c + d))) (GBR.mk Γ b c d v u') z)
                (fusionColumnCast_bcd_recast K Γ a b c d τ w'))
          have step3 : RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
                (FusionColumn (Γ.fuse a (b + c + d))) (GBR.mk Γ b c d v u')
                (MulOpposite.op τ • fusionColumnCast K Γ a (add_assoc b c d).symm w')
              = MulOpposite.op τ • gq4Close K Γ a b c d (RelTensor.mk K (Γ.D (c + d)).carrier
                  (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) v
                  (GBR.mk Γ a b (c + d) u' w')) :=
            (rightActionEnd_mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
                (FusionColumn (Γ.fuse a (b + c + d))) (MulOpposite.op τ) (GBR.mk Γ b c d v u')
                (fusionColumnCast K Γ a (add_assoc b c d).symm w')).symm.trans
              ((GQ4Total_op_smul_def K Γ a b c d τ _).symm.trans
                (congrArg (fun z : GQ4 K Γ a b c d => MulOpposite.op τ • z)
                  (gq4Close_mk K Γ a b c d v u' w').symm))
          exact step1.trans (step2.trans step3)
      | add x y hx hy =>
          calc gq4Close K Γ a b c d
                (rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                  (GBR Γ a b (c + d)) (MulOpposite.op τ) (RelTensor.mk K (Γ.D (c + d)).carrier
                    (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) v (x + y)))
              = gq4Close K Γ a b c d (RelTensor.mk K (Γ.D (c + d)).carrier
                  (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) v (MulOpposite.op τ • (x + y))) :=
                congrArg (gq4Close K Γ a b c d) (rightActionEnd_mk K (Γ.D (c + d)).carrier
                  (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) (MulOpposite.op τ) v (x + y))
            _ = gq4Close K Γ a b c d (RelTensor.mk K (Γ.D (c + d)).carrier
                  (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) v
                  (MulOpposite.op τ • x + MulOpposite.op τ • y)) :=
                congrArg (fun z => gq4Close K Γ a b c d (RelTensor.mk K (Γ.D (c + d)).carrier
                  (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) v z)) (smul_add _ _ _)
            _ = gq4Close K Γ a b c d (RelTensor.mk K (Γ.D (c + d)).carrier
                    (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) v (MulOpposite.op τ • x)
                  + RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                    (GBR Γ a b (c + d)) v (MulOpposite.op τ • y)) :=
                congrArg (gq4Close K Γ a b c d) (map_add
                  (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                    (GBR Γ a b (c + d)) v) _ _)
            _ = gq4Close K Γ a b c d (RelTensor.mk K (Γ.D (c + d)).carrier
                  (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) v (MulOpposite.op τ • x))
                + gq4Close K Γ a b c d (RelTensor.mk K (Γ.D (c + d)).carrier
                  (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) v (MulOpposite.op τ • y)) :=
                map_add _ _ _
            _ = MulOpposite.op τ • gq4Close K Γ a b c d (RelTensor.mk K (Γ.D (c + d)).carrier
                  (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) v x)
                + MulOpposite.op τ • gq4Close K Γ a b c d (RelTensor.mk K (Γ.D (c + d)).carrier
                  (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) v y) := congrArg₂ (· + ·) hx hy
            _ = MulOpposite.op τ • (gq4Close K Γ a b c d (RelTensor.mk K (Γ.D (c + d)).carrier
                    (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) v x)
                  + gq4Close K Γ a b c d (RelTensor.mk K (Γ.D (c + d)).carrier
                    (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) v y)) := (smul_add _ _ _).symm
            _ = MulOpposite.op τ • gq4Close K Γ a b c d (RelTensor.mk K (Γ.D (c + d)).carrier
                  (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) v (x + y)) :=
                congrArg _ ((map_add (gq4Close K Γ a b c d)
                    (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                      (GBR Γ a b (c + d)) v x)
                    (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                      (GBR Γ a b (c + d)) v y)).symm.trans
                  (congrArg (gq4Close K Γ a b c d) (map_add
                    (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                      (GBR Γ a b (c + d)) v) x y)).symm)
  | add x y hx hy =>
      calc gq4Close K Γ a b c d
            (rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
              (GBR Γ a b (c + d)) (MulOpposite.op τ) (x + y))
          = gq4Close K Γ a b c d
              (rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                  (GBR Γ a b (c + d)) (MulOpposite.op τ) x
                + rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                  (GBR Γ a b (c + d)) (MulOpposite.op τ) y) :=
            congrArg (gq4Close K Γ a b c d) (map_add
              (rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                (GBR Γ a b (c + d)) (MulOpposite.op τ)) x y)
        _ = gq4Close K Γ a b c d (rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
              (GBR Γ a b (c + d)) (MulOpposite.op τ) x)
            + gq4Close K Γ a b c d (rightActionEnd K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
              (GBR Γ a b (c + d)) (MulOpposite.op τ) y) := map_add _ _ _
        _ = MulOpposite.op τ • gq4Close K Γ a b c d x
            + MulOpposite.op τ • gq4Close K Γ a b c d y := congrArg₂ (· + ·) hx hy
        _ = MulOpposite.op τ • (gq4Close K Γ a b c d x + gq4Close K Γ a b c d y) :=
            (smul_add _ _ _).symm
        _ = MulOpposite.op τ • gq4Close K Γ a b c d (x + y) := congrArg _ (map_add _ _ _).symm

/-! ### Edges 2 and 7: the `GE2`-style genre -/

/-- **Edge 2** `E2M : V2 → V4`, `t_{a,b+c,d}|e` (owning faces `P6`, `PBC`;
presentation: `P6`, the whiskered `GE2` at the FIXED `gt2Canon (gTCanon Γ a
(b+c) d)`, `gChiCanon`'s own top-route second-edge datum). -/
noncomputable def E2M : V2 K Γ a b c d e →ₗ[K] V4 K Γ a b c d e :=
  RelTensor.map (GE2 K Γ a b c d (gParity K Γ a (b + c) d)
      (gt2Canon K Γ a b c d (gTCanon K Γ a (b + c) d)).toLinearMap
      (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
        (gTCanon_mem_gInterSpace K Γ a (b + c) d)))
    LinearMap.id (GE2_rightTotal K Γ a b c d) (fun _ _ => rfl)

theorem E2M_bijective : Function.Bijective (E2M K Γ a b c d e) :=
  PentagonB.RelTensor.map_bijective_left K
    (LinearEquiv.ofBijective
      (GE2 K Γ a b c d (gParity K Γ a (b + c) d)
        (gt2Canon K Γ a b c d (gTCanon K Γ a (b + c) d)).toLinearMap
        (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
          (gTCanon_mem_gInterSpace K Γ a (b + c) d)))
      ((PentagonB.smap_bijective K (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
          (gt2Canon K Γ a b c d (gTCanon K Γ a (b + c) d)) (gParity K Γ a (b + c) d)
          (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) d) (gParity K Γ a (b + c) d)
            (gTCanon_mem_gInterSpace K Γ a (b + c) d))).comp
        (gq2Assoc K Γ a b c d).bijective))
    (GE2_rightTotal K Γ a b c d)

/-- **Edge 7** `E7M : V11 → V13`, `a|t_{b,c+d,e}` (owning faces `P1`, `PCD`;
presentation: `P1`, the `V10..V14`-mirror of `GE2`, at the FIXED `gt2Canon
(gTCanon Γ b (c+d) e)`). -/
noncomputable def E7M : V11 K Γ a b c d e →ₗ[K] V13 K Γ a b c d e :=
  RelTensor.map (GE2 K Γ b c d e (gParity K Γ b (c + d) e)
      (gt2Canon K Γ b c d e (gTCanon K Γ b (c + d) e)).toLinearMap
      (gt2Canon_bcSlot K Γ (gTCanon K Γ b (c + d) e) (gParity K Γ b (c + d) e)
        (gTCanon_mem_gInterSpace K Γ b (c + d) e)))
    LinearMap.id (GE2_rightTotal K Γ b c d e) (fun _ _ => rfl)

theorem E7M_bijective : Function.Bijective (E7M K Γ a b c d e) :=
  PentagonB.RelTensor.map_bijective_left K
    (LinearEquiv.ofBijective
      (GE2 K Γ b c d e (gParity K Γ b (c + d) e)
        (gt2Canon K Γ b c d e (gTCanon K Γ b (c + d) e)).toLinearMap
        (gt2Canon_bcSlot K Γ (gTCanon K Γ b (c + d) e) (gParity K Γ b (c + d) e)
          (gTCanon_mem_gInterSpace K Γ b (c + d) e)))
      ((PentagonB.smap_bijective K (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
          (gt2Canon K Γ b c d e (gTCanon K Γ b (c + d) e)) (gParity K Γ b (c + d) e)
          (gt2Canon_bcSlot K Γ (gTCanon K Γ b (c + d) e) (gParity K Γ b (c + d) e)
            (gTCanon_mem_gInterSpace K Γ b (c + d) e))).comp
        (gq2Assoc K Γ b c d e).bijective))
    (GE2_rightTotal K Γ b c d e)

/-! ### Edges 5 and 10: the `GE5`+`gq4Close`-composite genre -/

/-- **The composite `gq4Close ∘ GE5`'s `Total`-equivariance**, at `(a,b,c,d)`
— `GE5_rightTotal` followed by `gq4Close_rightTotal`. -/
theorem E5MInner_rightTotal (a b c d : G) (τ : (Γ.D (a + b + c + d)).carrier)
    (m : GQ5 K Γ a b c d) :
    gq4Close K Γ a b c d (GE5 K Γ a b c d (gParity K Γ a b (c + d))
        (gTCanon K Γ a b (c + d)).toLinearMap (gCanonHphi5 K Γ a b c d) (MulOpposite.op τ • m))
      = MulOpposite.op τ • gq4Close K Γ a b c d (GE5 K Γ a b c d (gParity K Γ a b (c + d))
          (gTCanon K Γ a b (c + d)).toLinearMap (gCanonHphi5 K Γ a b c d) m) := by
  rw [GE5_rightTotal]
  exact gq4Close_rightTotal K Γ a b c d τ _

/-- **Edge 5** `E5M : V3 → V5`, `t_{a,b,c+d}|e` (owning faces `P6`, `PCD`;
presentation: `P6`, the whiskered `gq4Close ∘ GE5` at the FIXED `gTCanon Γ a
b (c+d)` — `GE5`'s codomain `GQ4r` closed onto `GQ4` by `gq4Close`). -/
noncomputable def E5M : V3 K Γ a b c d e →ₗ[K] V5 K Γ a b c d e :=
  RelTensor.map ((gq4Close K Γ a b c d).toLinearMap.comp (GE5 K Γ a b c d (gParity K Γ a b (c + d))
      (gTCanon K Γ a b (c + d)).toLinearMap (gCanonHphi5 K Γ a b c d)))
    LinearMap.id (E5MInner_rightTotal K Γ a b c d) (fun _ _ => rfl)

theorem E5M_bijective : Function.Bijective (E5M K Γ a b c d e) :=
  PentagonB.RelTensor.map_bijective_left K
    (LinearEquiv.ofBijective
      ((gq4Close K Γ a b c d).toLinearMap.comp (GE5 K Γ a b c d (gParity K Γ a b (c + d))
        (gTCanon K Γ a b (c + d)).toLinearMap (gCanonHphi5 K Γ a b c d)))
      ((gq4Close K Γ a b c d).bijective.comp
        ((PentagonB.smap_bijective K (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
            (gTCanon K Γ a b (c + d)) (gParity K Γ a b (c + d)) (gCanonHphi5 K Γ a b c d)).comp
          (gq5Swap K Γ a b c d).bijective)))
    (E5MInner_rightTotal K Γ a b c d)

/-- **Edge 10** `E10M : V12 → V14`, `a|t_{b,c,d+e}` (owning faces `P1`,
`PDE`; presentation: `P1`, the `V10..V14`-mirror of `E5M`, at the FIXED
`gTCanon Γ b c (d+e)`). -/
noncomputable def E10M : V12 K Γ a b c d e →ₗ[K] V14 K Γ a b c d e :=
  RelTensor.map ((gq4Close K Γ b c d e).toLinearMap.comp (GE5 K Γ b c d e (gParity K Γ b c (d + e))
      (gTCanon K Γ b c (d + e)).toLinearMap (gCanonHphi5 K Γ b c d e)))
    LinearMap.id (E5MInner_rightTotal K Γ b c d e) (fun _ _ => rfl)

theorem E10M_bijective : Function.Bijective (E10M K Γ a b c d e) :=
  PentagonB.RelTensor.map_bijective_left K
    (LinearEquiv.ofBijective
      ((gq4Close K Γ b c d e).toLinearMap.comp (GE5 K Γ b c d e (gParity K Γ b c (d + e))
        (gTCanon K Γ b c (d + e)).toLinearMap (gCanonHphi5 K Γ b c d e)))
      ((gq4Close K Γ b c d e).bijective.comp
        ((PentagonB.smap_bijective K (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
            (gTCanon K Γ b c (d + e)) (gParity K Γ b c (d + e)) (gCanonHphi5 K Γ b c d e)).comp
          (gq5Swap K Γ b c d e).bijective)))
    (E5MInner_rightTotal K Γ b c d e)

end GaugeChi

end Superfusion
