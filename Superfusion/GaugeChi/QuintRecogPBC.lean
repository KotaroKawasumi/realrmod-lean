/-
Superfusion / GaugeChi / QuintRecogPBC

The five edge recognitions for the `(b+c)`-cluster pentagon face.  Each
identity conjugates an original quintuple edge by the sign-free
`omegaPbcV*` extraction equivalences and obtains the corresponding
signed amplification of a canonical pentagon edge at `(a,b+c,d,e)`.
-/
import Superfusion.GaugeChi.QuintExtractPBC

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

/-! ### Edge 2 -/

private noncomputable def pbcV4Gen
    (u : FusionColumn (Γ.fuse b c)) (m : GQ3Inner K Γ a b c d)
    (t : FusionColumn (Γ.fuse (a + b + c + d) e)) : V4 K Γ a b c d e :=
  RelTensor.mk K (Γ.D (a + b + c + d)).carrier
    (GQ3 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
    (GQ3.mk K Γ a b c d u m) t

private theorem E2M_leaf_pbc_typed {ju : ZMod 2}
    {u : FusionColumn (Γ.fuse b c)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse b c) ju)
    (v : FusionColumn (Γ.fuse a (b + c)))
    (x : FusionColumn (Γ.fuse (a + b + c) d))
    (t : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    E2M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (GQ2 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) x) t)
      = ((sgn (gParity K Γ a (b + c) d * ju) : ℤˣ) : ℤ) •
          pbcV4Gen K Γ a b c d e u
            (gt2Canon K Γ a b c d (gTCanon K Γ a (b + c) d)
              (RelTensor.mk K (Γ.D (a + b + c)).carrier
                (FusionColumn (Γ.fuse a (b + c)))
                (FusionColumn (Γ.fuse (a + b + c) d)) v x)) t :=
  E2M_leaf K Γ a b c d e hu v x t

private theorem omegaPbcV4_gen
    (u : FusionColumn (Γ.fuse b c)) (m : GQ3Inner K Γ a b c d)
    (t : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    omegaPbcV4 K Γ a b c d e (pbcV4Gen K Γ a b c d e u m t)
      = RelTensor.mk K (Γ.D (b + c)).carrier
          (FusionColumn (Γ.fuse b c)) (GQ2 K Γ a (b + c) d e) u
          (GQ2.mk K Γ a (b + c) d e m
            (gColumnCastFst K Γ e (pbcHeq a b c d) t)) :=
  omegaPbcV4_mk K Γ a b c d e u m t

private theorem recog_E2M_pbc_generator {ju : ZMod 2}
    {u : FusionColumn (Γ.fuse b c)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse b c) ju)
    (v : FusionColumn (Γ.fuse a (b + c)))
    (x : FusionColumn (Γ.fuse (a + b + c) d))
    (t : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    omegaPbcV4 K Γ a b c d e
        (E2M K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
            (GQ2 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
            (GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) x) t))
      = smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
          (GE1 K Γ a (b + c) d e
            (gTCanon K Γ a (b + c) d).toLinearMap
            (gCanonRight K Γ a (b + c) d))
          (gParity K Γ a (b + c) d) (pbcHg1 K Γ a b c d e)
          (omegaPbcV2 K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
              (GQ2 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
              (GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) x) t)) := by
  rw [E2M_leaf_pbc_typed K Γ a b c d e hu v x t, map_zsmul,
    omegaPbcV4_gen, omegaPbcV2_mk, gblOuterCastV2_mk,
    smap_mk_of_mem (Γ.D (b + c)).grading
      (FusionColumn.grading (Γ.fuse b c))
      (GE1 K Γ a (b + c) d e
        (gTCanon K Γ a (b + c) d).toLinearMap
        (gCanonRight K Γ a (b + c) d))
      (gParity K Γ a (b + c) d) (pbcHg1 K Γ a b c d e) hu,
    GE1_mk, gt2Canon_mk]
  rfl

/-- Edge 2 becomes the first pentagon edge after extracting `F_{b,c}`. -/
theorem recog_E2M_pbc :
    (omegaPbcV4 K Γ a b c d e).toLinearMap ∘ₗ E2M K Γ a b c d e
      = smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
          (GE1 K Γ a (b + c) d e
            (gTCanon K Γ a (b + c) d).toLinearMap
            (gCanonRight K Γ a (b + c) d))
          (gParity K Γ a (b + c) d) (pbcHg1 K Γ a b c d e)
          ∘ₗ (omegaPbcV2 K Γ a b c d e).toLinearMap := by
  refine RelTensor.hom_ext fun m t => ?_
  induction m using GQ2.induction_on_gen K Γ a b c d with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add m m' hm hm' => simp only [map_add, LinearMap.add_apply, hm, hm']
  | homog u v x hu =>
      exact recog_E2M_pbc_generator K Γ a b c d e hu v x t

/-! ### Edge 9 -/

private noncomputable def pbcV12Gen
    (u : FusionColumn (Γ.fuse b c)) (q : GBR Γ (b + c) d e)
    (t : FusionColumn (Γ.fuse a (b + c + d + e))) : V12 K Γ a b c d e :=
  RelTensor.mk K (Γ.D (b + c + d + e)).carrier
    (GQ5 K Γ b c d e) (FusionColumn (Γ.fuse a (b + c + d + e)))
    (GQ5.mk K Γ b c d e u q) t

private theorem E9M_leaf_pbc_typed {ju : ZMod 2}
    {u : FusionColumn (Γ.fuse b c)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse b c) ju)
    (v : FusionColumn (Γ.fuse (b + c) d))
    (w : FusionColumn (Γ.fuse (b + c + d) e))
    (t : FusionColumn (Γ.fuse a (b + c + d + e))) :
    E9M K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (GQ1 K Γ b c d e) (FusionColumn (Γ.fuse a (b + c + d + e)))
          (GQ1.mk K Γ b c d e (GBL.mk Γ b c d u v) w) t)
      = ((sgn (gParity K Γ (b + c) d e * ju) : ℤˣ) : ℤ) •
          pbcV12Gen K Γ a b c d e u
            (gTCanon K Γ (b + c) d e (GBL.mk Γ (b + c) d e v w)) t :=
  E9M_leaf K Γ a b c d e hu v w t

private theorem omegaPbcV12_gen
    (u : FusionColumn (Γ.fuse b c)) (q : GBR Γ (b + c) d e)
    (t : FusionColumn (Γ.fuse a (b + c + d + e))) :
    omegaPbcV12 K Γ a b c d e (pbcV12Gen K Γ a b c d e u q t)
      = RelTensor.mk K (Γ.D (b + c)).carrier
          (FusionColumn (Γ.fuse b c)) (GQ4 K Γ a (b + c) d e) u
          (GQ4.mk K Γ a (b + c) d e q t) :=
  omegaPbcV12_mk K Γ a b c d e u q t

private theorem GE3_pbc_mk
    (v : FusionColumn (Γ.fuse (b + c) d))
    (w : FusionColumn (Γ.fuse (b + c + d) e))
    (t : FusionColumn (Γ.fuse a (b + c + d + e))) :
    GE3 K Γ a (b + c) d e
        (gTCanon K Γ (b + c) d e).toLinearMap
        (gCanonRight K Γ (b + c) d e)
        (GQ3.mk K Γ a (b + c) d e v
          (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
            (FusionColumn (Γ.fuse (b + c + d) e))
            (FusionColumn (Γ.fuse a (b + c + d + e))) w t))
      = GQ4.mk K Γ a (b + c) d e
          (gTCanon K Γ (b + c) d e (GBL.mk Γ (b + c) d e v w)) t :=
  GE3_mk K Γ a (b + c) d e
    (gTCanon K Γ (b + c) d e).toLinearMap
    (gCanonRight K Γ (b + c) d e) v w t

private theorem recog_E9M_pbc_generator {ju : ZMod 2}
    {u : FusionColumn (Γ.fuse b c)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse b c) ju)
    (v : FusionColumn (Γ.fuse (b + c) d))
    (w : FusionColumn (Γ.fuse (b + c + d) e))
    (t : FusionColumn (Γ.fuse a (b + c + d + e))) :
    omegaPbcV12 K Γ a b c d e
        (E9M K Γ a b c d e
          (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
            (GQ1 K Γ b c d e) (FusionColumn (Γ.fuse a (b + c + d + e)))
            (GQ1.mk K Γ b c d e (GBL.mk Γ b c d u v) w) t))
      = smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
          (GE3 K Γ a (b + c) d e
            (gTCanon K Γ (b + c) d e).toLinearMap
            (gCanonRight K Γ (b + c) d e))
          (gParity K Γ (b + c) d e) (pbcHg3 K Γ a b c d e)
          (omegaPbcV10 K Γ a b c d e
            (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
              (GQ1 K Γ b c d e) (FusionColumn (Γ.fuse a (b + c + d + e)))
              (GQ1.mk K Γ b c d e (GBL.mk Γ b c d u v) w) t)) := by
  rw [E9M_leaf_pbc_typed K Γ a b c d e hu v w t, map_zsmul,
    omegaPbcV12_gen, omegaPbcV10_mk,
    smap_mk_of_mem (Γ.D (b + c)).grading
      (FusionColumn.grading (Γ.fuse b c))
      (GE3 K Γ a (b + c) d e
        (gTCanon K Γ (b + c) d e).toLinearMap
        (gCanonRight K Γ (b + c) d e))
      (gParity K Γ (b + c) d e) (pbcHg3 K Γ a b c d e) hu,
    GE3_pbc_mk]

/-- Edge 9 becomes the third pentagon edge after extracting `F_{b,c}`. -/
theorem recog_E9M_pbc :
    (omegaPbcV12 K Γ a b c d e).toLinearMap ∘ₗ E9M K Γ a b c d e
      = smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
          (GE3 K Γ a (b + c) d e
            (gTCanon K Γ (b + c) d e).toLinearMap
            (gCanonRight K Γ (b + c) d e))
          (gParity K Γ (b + c) d e) (pbcHg3 K Γ a b c d e)
          ∘ₗ (omegaPbcV10 K Γ a b c d e).toLinearMap := by
  refine RelTensor.hom_ext fun m t => ?_
  induction m using GQ1.induction_on_gen K Γ b c d e with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add m m' hm hm' => simp only [map_add, LinearMap.add_apply, hm, hm']
  | homog u v w hu =>
      exact recog_E9M_pbc_generator K Γ a b c d e hu v w t

/-! ### Edge 15 -/

private theorem pbc_E15_inner_cast
    (v : FusionColumn (Γ.fuse (b + c) d))
    (x : FusionColumn (Γ.fuse a (b + c + d)))
    (t : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    pbcV10GQ3Gen K Γ a b c d e v
        (gTCanon K Γ a (b + c + d) e
          (GBL.mk Γ a (b + c + d) e x
            (gColumnCastFst K Γ e (add_assoc_four a b c d) t)))
      = GQ3.mk K Γ a (b + c) d e v
          (gt2Canon K Γ a (b + c) d e
            (gTCanon K Γ a (b + c + d) e)
            (RelTensor.mk K (Γ.D (a + (b + c) + d)).carrier
              (FusionColumn (Γ.fuse a (b + c + d)))
              (FusionColumn (Γ.fuse (a + (b + c) + d) e)) x
              (gColumnCastFst K Γ e (pbcHeq a b c d) t))) := by
  rw [pbcV10GQ3Gen_eq, gt2Canon_mk]
  congr 3
  exact (gColumnCastFst_trans K Γ e (pbcHeq a b c d)
    (add_assoc a (b + c) d) t).symm

private theorem GE2_pbc_mk {jv : ZMod 2}
    {v : FusionColumn (Γ.fuse (b + c) d)}
    (hv : v ∈ FusionColumn.grading (Γ.fuse (b + c) d) jv)
    (x : FusionColumn (Γ.fuse a (b + c + d)))
    (t : FusionColumn (Γ.fuse (a + (b + c) + d) e)) :
    GE2 K Γ a (b + c) d e
        (gParity K Γ a (b + c + d) e)
        (gt2Canon K Γ a (b + c) d e
          (gTCanon K Γ a (b + c + d) e)).toLinearMap
        (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c + d) e)
          (gParity K Γ a (b + c + d) e)
          (gTCanon_mem_gInterSpace K Γ a (b + c + d) e))
        (GQ2.mk K Γ a (b + c) d e (GBR.mk Γ a (b + c) d v x) t)
      = ((sgn (gParity K Γ a (b + c + d) e * jv) : ℤˣ) : ℤ) •
          GQ3.mk K Γ a (b + c) d e v
            (gt2Canon K Γ a (b + c) d e
              (gTCanon K Γ a (b + c + d) e)
              (RelTensor.mk K (Γ.D (a + (b + c) + d)).carrier
                (FusionColumn (Γ.fuse a (b + c + d)))
                (FusionColumn (Γ.fuse (a + (b + c) + d) e)) x t)) :=
  GE2_mk_of_mem K Γ a (b + c) d e
    (gParity K Γ a (b + c + d) e)
    (gt2Canon K Γ a (b + c) d e
      (gTCanon K Γ a (b + c + d) e)).toLinearMap
    (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c + d) e)
      (gParity K Γ a (b + c + d) e)
      (gTCanon_mem_gInterSpace K Γ a (b + c + d) e)) hv x t

private theorem recog_E15M_pbc_generator {ju jv : ZMod 2}
    {u : FusionColumn (Γ.fuse b c)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse b c) ju)
    {v : FusionColumn (Γ.fuse (b + c) d)}
    (hv : v ∈ FusionColumn.grading (Γ.fuse (b + c) d) jv)
    (x : FusionColumn (Γ.fuse a (b + c + d)))
    (t : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    omegaPbcV10 K Γ a b c d e
        (E15M K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
            (GQ3 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
            (GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v x)) t))
      = smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
          (GE2 K Γ a (b + c) d e
            (gParity K Γ a (b + c + d) e)
            (gt2Canon K Γ a (b + c) d e
              (gTCanon K Γ a (b + c + d) e)).toLinearMap
            (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c + d) e)
              (gParity K Γ a (b + c + d) e)
              (gTCanon_mem_gInterSpace K Γ a (b + c + d) e)))
          (gParity K Γ a (b + c + d) e) (pbcHg2 K Γ a b c d e)
          (omegaPbcV4 K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
              (GQ3 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
              (GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v x)) t)) := by
  have sign_id : ∀ p i j : ZMod 2, p * (i + j) = p * i + p * j := by decide
  rw [E15M_leaf_pbc K Γ a b c d e hu hv x t, map_zsmul,
    omegaPbcV10_gV10Assoc_symm_mk, omegaPbcV4_mk,
    smap_mk_of_mem (Γ.D (b + c)).grading
      (FusionColumn.grading (Γ.fuse b c))
      (GE2 K Γ a (b + c) d e
        (gParity K Γ a (b + c + d) e)
        (gt2Canon K Γ a (b + c) d e
          (gTCanon K Γ a (b + c + d) e)).toLinearMap
        (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c + d) e)
          (gParity K Γ a (b + c + d) e)
          (gTCanon_mem_gInterSpace K Γ a (b + c + d) e)))
      (gParity K Γ a (b + c + d) e) (pbcHg2 K Γ a b c d e) hu,
    GE2_pbc_mk K Γ a b c d e hv,
    map_zsmul, smul_smul, ← Units.val_mul, ← sgn_add, ← sign_id,
    pbc_E15_inner_cast]

/-- Edge 15 becomes the second pentagon edge after extracting `F_{b,c}`. -/
theorem recog_E15M_pbc :
    (omegaPbcV10 K Γ a b c d e).toLinearMap ∘ₗ E15M K Γ a b c d e
      = smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
          (GE2 K Γ a (b + c) d e
            (gParity K Γ a (b + c + d) e)
            (gt2Canon K Γ a (b + c) d e
              (gTCanon K Γ a (b + c + d) e)).toLinearMap
            (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c + d) e)
              (gParity K Γ a (b + c + d) e)
              (gTCanon_mem_gInterSpace K Γ a (b + c + d) e)))
          (gParity K Γ a (b + c + d) e) (pbcHg2 K Γ a b c d e)
          ∘ₗ (omegaPbcV4 K Γ a b c d e).toLinearMap := by
  refine RelTensor.hom_ext fun m t => ?_
  induction m using GQ3.induction_on_gen2 K Γ a b c d with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add m m' hm hm' => simp only [map_add, LinearMap.add_apply, hm, hm']
  | homog u v x hu hv =>
      exact recog_E15M_pbc_generator K Γ a b c d e hu hv x t

/-! ### Edge 16 -/

private theorem pbc_E16_inner_cast
    (x : FusionColumn (Γ.fuse (a + b + c) d))
    (t : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    gGbrCastFst K Γ d e (add_assoc a b c)
        (gTCanon K Γ (a + b + c) d e
          (GBL.mk Γ (a + b + c) d e x t))
      = gTCanon K Γ (a + (b + c)) d e
          (GBL.mk Γ (a + (b + c)) d e
            (gColumnCastFst K Γ d (add_assoc a b c) x)
            (gColumnCastFst K Γ e (pbcHeq a b c d) t)) :=
  gTCanon_cast_fst_mk K Γ d e (add_assoc a b c) x t

private theorem GE4_pbc_mk {jv : ZMod 2}
    {v : FusionColumn (Γ.fuse a (b + c))}
    (hv : v ∈ FusionColumn.grading (Γ.fuse a (b + c)) jv)
    (x : FusionColumn (Γ.fuse (a + (b + c)) d))
    (t : FusionColumn (Γ.fuse (a + (b + c) + d) e)) :
    GE4 K Γ a (b + c) d e
        (gParity K Γ (a + (b + c)) d e)
        (gTCanon K Γ (a + (b + c)) d e).toLinearMap
        (gCanonHphi4 K Γ a (b + c) d e)
        (RelTensor.mk K (Γ.D (a + (b + c) + d)).carrier
          (GBL Γ a (b + c) d)
          (FusionColumn (Γ.fuse (a + (b + c) + d) e))
          (GBL.mk Γ a (b + c) d v x) t)
      = ((sgn (gParity K Γ (a + (b + c)) d e * jv) : ℤˣ) : ℤ) •
          GQ5.mk K Γ a (b + c) d e v
            (gTCanon K Γ (a + (b + c)) d e
              (GBL.mk Γ (a + (b + c)) d e x t)) :=
  GE4_mk_of_mem K Γ a (b + c) d e
    (gParity K Γ (a + (b + c)) d e)
    (gTCanon K Γ (a + (b + c)) d e).toLinearMap
    (gCanonHphi4 K Γ a (b + c) d e) hv x t

private noncomputable def pbcV7Gen
    (m : GBR Γ a b c) (n : GBR Γ (a + b + c) d e) :
    V7 K Γ a b c d e :=
  RelTensor.mk K (Γ.D (a + b + c)).carrier
    (GBR Γ a b c) (GBR Γ (a + b + c) d e) m n

private theorem E16M_general_pbc_typed {ju jv : ZMod 2}
    {u : FusionColumn (Γ.fuse b c)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse b c) ju)
    {v : FusionColumn (Γ.fuse a (b + c))}
    (hv : v ∈ FusionColumn.grading (Γ.fuse a (b + c)) jv)
    (x : FusionColumn (Γ.fuse (a + b + c) d))
    (t : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    E16M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (GQ2 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) x) t)
      = ((sgn (gParity K Γ (a + b + c) d e * (ju + jv)) : ℤˣ) : ℤ) •
          pbcV7Gen K Γ a b c d e (GBR.mk Γ a b c u v)
            (gTCanon K Γ (a + b + c) d e
              (GBL.mk Γ (a + b + c) d e x t)) :=
  E16M_general K Γ a b c d e
    (GBR.mk_mem_grading Γ a b c hu hv) x t

private theorem omegaPbcV7_gen
    (u : FusionColumn (Γ.fuse b c))
    (v : FusionColumn (Γ.fuse a (b + c)))
    (n : GBR Γ (a + b + c) d e) :
    omegaPbcV7 K Γ a b c d e
        (pbcV7Gen K Γ a b c d e (GBR.mk Γ a b c u v) n)
      = RelTensor.mk K (Γ.D (b + c)).carrier
          (FusionColumn (Γ.fuse b c)) (GQ5 K Γ a (b + c) d e) u
          (GQ5.mk K Γ a (b + c) d e v
            (gGbrCastFst K Γ d e (add_assoc a b c) n)) :=
  omegaPbcV7_mk K Γ a b c d e u v n

private theorem recog_E16M_pbc_generator {ju jv : ZMod 2}
    {u : FusionColumn (Γ.fuse b c)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse b c) ju)
    {v : FusionColumn (Γ.fuse a (b + c))}
    (hv : v ∈ FusionColumn.grading (Γ.fuse a (b + c)) jv)
    (x : FusionColumn (Γ.fuse (a + b + c) d))
    (t : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    omegaPbcV7 K Γ a b c d e
        (E16M K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
            (GQ2 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
            (GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) x) t))
      = smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
          (GE4 K Γ a (b + c) d e
            (gParity K Γ (a + (b + c)) d e)
            (gTCanon K Γ (a + (b + c)) d e).toLinearMap
            (gCanonHphi4 K Γ a (b + c) d e))
          (gParity K Γ (a + (b + c)) d e) (pbcHg4 K Γ a b c d e)
          (omegaPbcV2 K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
              (GQ2 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
              (GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) x) t)) := by
  have hp : gParity K Γ (a + b + c) d e
      = gParity K Γ (a + (b + c)) d e :=
    congrArg (fun z => gParity K Γ z d e) (add_assoc a b c)
  have sign_id : ∀ p i j : ZMod 2, p * (i + j) = p * i + p * j := by decide
  rw [E16M_general_pbc_typed K Γ a b c d e hu hv x t,
    map_zsmul, omegaPbcV7_gen, omegaPbcV2_mk, gblOuterCastV2_mk,
    smap_mk_of_mem (Γ.D (b + c)).grading
      (FusionColumn.grading (Γ.fuse b c))
      (GE4 K Γ a (b + c) d e
        (gParity K Γ (a + (b + c)) d e)
        (gTCanon K Γ (a + (b + c)) d e).toLinearMap
        (gCanonHphi4 K Γ a (b + c) d e))
      (gParity K Γ (a + (b + c)) d e) (pbcHg4 K Γ a b c d e) hu,
    GE4_pbc_mk K Γ a b c d e hv, map_zsmul,
    pbc_E16_inner_cast, smul_smul, ← Units.val_mul, ← sgn_add,
    ← sign_id, hp]

/-- Edge 16 becomes the fourth pentagon edge after extracting `F_{b,c}`. -/
theorem recog_E16M_pbc :
    (omegaPbcV7 K Γ a b c d e).toLinearMap ∘ₗ E16M K Γ a b c d e
      = smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
          (GE4 K Γ a (b + c) d e
            (gParity K Γ (a + (b + c)) d e)
            (gTCanon K Γ (a + (b + c)) d e).toLinearMap
            (gCanonHphi4 K Γ a (b + c) d e))
          (gParity K Γ (a + (b + c)) d e) (pbcHg4 K Γ a b c d e)
          ∘ₗ (omegaPbcV2 K Γ a b c d e).toLinearMap := by
  refine RelTensor.hom_ext fun m t => ?_
  induction m using GQ2.induction_on_gen2 K Γ a b c d with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add m m' hm hm' => simp only [map_add, LinearMap.add_apply, hm, hm']
  | homog u v x hu hv =>
      exact recog_E16M_pbc_generator K Γ a b c d e hu hv x t

/-! ### Edge 17 -/

private theorem E17M_leaf_pbc_typed {ju jv jw : ZMod 2}
    {u : FusionColumn (Γ.fuse b c)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse b c) ju)
    {v : FusionColumn (Γ.fuse a (b + c))}
    (hv : v ∈ FusionColumn.grading (Γ.fuse a (b + c)) jv)
    {w : FusionColumn (Γ.fuse d e)}
    (hw : w ∈ FusionColumn.grading (Γ.fuse d e) jw)
    (q : FusionColumn (Γ.fuse (a + b + c) (d + e))) :
    E17M K Γ a b c d e
        (pbcV7Gen K Γ a b c d e
          (GBR.mk Γ a b c u v) (GBR.mk Γ (a + b + c) d e w q))
      = ((sgn (jw * jv
            + gParity K Γ a (b + c) (d + e) * (ju + jw)) : ℤˣ) : ℤ) •
          (gV12Assoc K Γ a b c d e).symm
            (RelTensor.mk K (Γ.D (b + c)).carrier
              (FusionColumn (Γ.fuse b c)) (GQ4 K Γ a (b + c) d e) u
              (gq4Close K Γ a (b + c) d e
                (GQ4r.mk K Γ a (b + c) d e w
                  (gt2Canon K Γ a b c (d + e)
                    (gTCanon K Γ a (b + c) (d + e))
                    (RelTensor.mk K (Γ.D (a + b + c)).carrier
                      (FusionColumn (Γ.fuse a (b + c)))
                      (FusionColumn (Γ.fuse (a + b + c) (d + e))) v q))))) :=
  E17M_leaf K Γ a b c d e hu hv hw q

private theorem omegaPbcV12_gV12Assoc_symm
    (z : RelTensor K (Γ.D (b + c)).carrier
      (FusionColumn (Γ.fuse b c)) (GQ4 K Γ a (b + c) d e)) :
    omegaPbcV12 K Γ a b c d e ((gV12Assoc K Γ a b c d e).symm z) = z :=
  (gV12Assoc K Γ a b c d e).apply_symm_apply z

private theorem GE5_pbc_mk {jv jw : ZMod 2}
    {v : FusionColumn (Γ.fuse a (b + c))}
    (hv : v ∈ FusionColumn.grading (Γ.fuse a (b + c)) jv)
    {w : FusionColumn (Γ.fuse d e)}
    (hw : w ∈ FusionColumn.grading (Γ.fuse d e) jw)
    (q : FusionColumn (Γ.fuse (a + (b + c)) (d + e))) :
    GE5 K Γ a (b + c) d e
        (gParity K Γ a (b + c) (d + e))
        (gTCanon K Γ a (b + c) (d + e)).toLinearMap
        (gCanonHphi5 K Γ a (b + c) d e)
        (GQ5.mk K Γ a (b + c) d e v
          (GBR.mk Γ (a + (b + c)) d e w q))
      = ((sgn (jw * (gParity K Γ a (b + c) (d + e) + jv)) : ℤˣ) : ℤ) •
          GQ4r.mk K Γ a (b + c) d e w
            (gTCanon K Γ a (b + c) (d + e)
              (GBL.mk Γ a (b + c) (d + e) v q)) :=
  GE5_mk_of_mem K Γ a (b + c) d e
    (gParity K Γ a (b + c) (d + e))
    (gTCanon K Γ a (b + c) (d + e)).toLinearMap
    (gCanonHphi5 K Γ a (b + c) d e) hw hv q

private theorem pbcE17Map_mk {jv jw : ZMod 2}
    {v : FusionColumn (Γ.fuse a (b + c))}
    (hv : v ∈ FusionColumn.grading (Γ.fuse a (b + c)) jv)
    {w : FusionColumn (Γ.fuse d e)}
    (hw : w ∈ FusionColumn.grading (Γ.fuse d e) jw)
    (q : FusionColumn (Γ.fuse (a + (b + c)) (d + e))) :
    pbcE17Map K Γ a b c d e
        (GQ5.mk K Γ a (b + c) d e v
          (GBR.mk Γ (a + (b + c)) d e w q))
      = ((sgn (jw * (gParity K Γ a (b + c) (d + e) + jv)) : ℤˣ) : ℤ) •
          gq4Close K Γ a (b + c) d e
            (GQ4r.mk K Γ a (b + c) d e w
              (gTCanon K Γ a (b + c) (d + e)
                (GBL.mk Γ a (b + c) (d + e) v q))) := by
  show gq4Close K Γ a (b + c) d e
      (GE5 K Γ a (b + c) d e
        (gParity K Γ a (b + c) (d + e))
        (gTCanon K Γ a (b + c) (d + e)).toLinearMap
        (gCanonHphi5 K Γ a (b + c) d e)
        (GQ5.mk K Γ a (b + c) d e v
          (GBR.mk Γ (a + (b + c)) d e w q))) = _
  rw [GE5_pbc_mk K Γ a b c d e hv hw, map_zsmul]

private theorem pbc_E17_inner_cast
    (v : FusionColumn (Γ.fuse a (b + c)))
    (q : FusionColumn (Γ.fuse (a + b + c) (d + e))) :
    gt2Canon K Γ a b c (d + e)
        (gTCanon K Γ a (b + c) (d + e))
        (RelTensor.mk K (Γ.D (a + b + c)).carrier
          (FusionColumn (Γ.fuse a (b + c)))
          (FusionColumn (Γ.fuse (a + b + c) (d + e))) v q)
      = gTCanon K Γ a (b + c) (d + e)
          (GBL.mk Γ a (b + c) (d + e) v
            (gColumnCastFst K Γ (d + e) (add_assoc a b c) q)) :=
  gt2Canon_mk K Γ a b c (d + e)
    (gTCanon K Γ a (b + c) (d + e)) v q

private theorem recog_E17M_pbc_generator {ju jv jw : ZMod 2}
    {u : FusionColumn (Γ.fuse b c)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse b c) ju)
    {v : FusionColumn (Γ.fuse a (b + c))}
    (hv : v ∈ FusionColumn.grading (Γ.fuse a (b + c)) jv)
    {w : FusionColumn (Γ.fuse d e)}
    (hw : w ∈ FusionColumn.grading (Γ.fuse d e) jw)
    (q : FusionColumn (Γ.fuse (a + b + c) (d + e))) :
    omegaPbcV12 K Γ a b c d e
        (E17M K Γ a b c d e
          (pbcV7Gen K Γ a b c d e
            (GBR.mk Γ a b c u v) (GBR.mk Γ (a + b + c) d e w q)))
      = smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
          (pbcE17Map K Γ a b c d e)
          (gParity K Γ a (b + c) (d + e))
          (pbcE17Map_hg K Γ a b c d e)
          (omegaPbcV7 K Γ a b c d e
            (pbcV7Gen K Γ a b c d e
              (GBR.mk Γ a b c u v) (GBR.mk Γ (a + b + c) d e w q))) := by
  have sign_id : ∀ p i j k : ZMod 2,
      k * j + p * (i + k) = p * i + k * (p + j) := by decide
  rw [E17M_leaf_pbc_typed K Γ a b c d e hu hv hw q,
    map_zsmul, omegaPbcV12_gV12Assoc_symm,
    omegaPbcV7_gen, gGbrCastFst_mk,
    smap_mk_of_mem (Γ.D (b + c)).grading
      (FusionColumn.grading (Γ.fuse b c))
      (pbcE17Map K Γ a b c d e)
      (gParity K Γ a (b + c) (d + e))
      (pbcE17Map_hg K Γ a b c d e) hu,
    pbcE17Map_mk K Γ a b c d e hv hw, map_zsmul,
    pbc_E17_inner_cast, smul_smul, ← Units.val_mul, ← sgn_add,
    sign_id]

/-- Edge 17 becomes the fifth pentagon edge after extracting `F_{b,c}`. -/
theorem recog_E17M_pbc :
    (omegaPbcV12 K Γ a b c d e).toLinearMap ∘ₗ E17M K Γ a b c d e
      = smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
          (pbcE17Map K Γ a b c d e)
          (gParity K Γ a (b + c) (d + e))
          (pbcE17Map_hg K Γ a b c d e)
          ∘ₗ (omegaPbcV7 K Γ a b c d e).toLinearMap := by
  refine RelTensor.hom_ext fun m n => ?_
  induction n using GBR.induction_on_left_homog K Γ (a + b + c) d e with
  | zero => simp only [map_zero]
  | add n n' hn hn' => simp only [map_add, hn, hn']
  | homog jw w q hw =>
      induction m using GBR.induction_on_gen2 K Γ a b c with
      | zero => simp only [map_zero, LinearMap.zero_apply]
      | add m m' hm hm' => simp only [map_add, LinearMap.add_apply, hm, hm']
      | homog u v hu hv =>
          exact recog_E17M_pbc_generator K Γ a b c d e hu hv hw q

end GaugeChi

end Superfusion
