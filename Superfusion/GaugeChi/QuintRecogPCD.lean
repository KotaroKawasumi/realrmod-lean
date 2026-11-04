/-
Superfusion / GaugeChi / QuintRecogPCD

Recognition of the five edges of the `(c+d)`-cluster pentagon face.
The common spectator is `F_{c,d}` and the residual pentagon is the
canonical one at `(a,b,c+d,e)`.
-/
import Superfusion.GaugeChi.QuintExtractPCD
import Superfusion.GaugeChi.QuintExtract8
import Superfusion.GaugeChi.QuintRecog2
import Superfusion.GaugeChi.QuintRecog5

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

/-! ### The shifted canonical pentagon edges -/

noncomputable def pcdGE1 :
    GQ1 K Γ a b (c + d) e →ₗ[K] GQ2 K Γ a b (c + d) e :=
  GE1 K Γ a b (c + d) e (gTCanon K Γ a b (c + d)).toLinearMap
    (gCanonRight K Γ a b (c + d))

noncomputable def pcdGE2 :
    GQ2 K Γ a b (c + d) e →ₗ[K] GQ3 K Γ a b (c + d) e :=
  GE2 K Γ a b (c + d) e (gParity K Γ a (b + (c + d)) e)
    (gt2Canon K Γ a b (c + d) e
      (gTCanon K Γ a (b + (c + d)) e)).toLinearMap
    (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + (c + d)) e)
      (gParity K Γ a (b + (c + d)) e)
      (gTCanon_mem_gInterSpace K Γ a (b + (c + d)) e))

noncomputable def pcdGE3 :
    GQ3 K Γ a b (c + d) e →ₗ[K] GQ4 K Γ a b (c + d) e :=
  GE3 K Γ a b (c + d) e (gTCanon K Γ b (c + d) e).toLinearMap
    (gCanonRight K Γ b (c + d) e)

noncomputable def pcdGE4 :
    GQ1 K Γ a b (c + d) e →ₗ[K] GQ5 K Γ a b (c + d) e :=
  GE4 K Γ a b (c + d) e (gParity K Γ (a + b) (c + d) e)
    (gTCanon K Γ (a + b) (c + d) e).toLinearMap
    (gCanonHphi4 K Γ a b (c + d) e)

/-- The shifted fifth edge, including the canonical closing map. -/
noncomputable def pcdE19Map :
    GQ5 K Γ a b (c + d) e →ₗ[K] GQ4 K Γ a b (c + d) e :=
  (gq4Close K Γ a b (c + d) e).toLinearMap.comp
    (GE5 K Γ a b (c + d) e
      (gParity K Γ a b (c + d + e))
      (gTCanon K Γ a b (c + d + e)).toLinearMap
      (gCanonHphi5 K Γ a b (c + d) e))

/-! ### Signed equivariance in the extracted `D_{c+d}` slot -/

theorem pcdHg1 :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (c + d)).carrier⦄,
      τ ∈ (Γ.D (c + d)).grading i →
      ∀ n : GQ1 K Γ a b (c + d) e,
        pcdGE1 K Γ a b c d e (τ • n)
          = ((sgn (gParity K Γ a b (c + d) * i) : ℤˣ) : ℤ) •
              (τ • pcdGE1 K Γ a b c d e n) :=
  fun _i _τ hτ n => GE1.comp_cslot K Γ a b (c + d) e
    (gTCanon K Γ a b (c + d)).toLinearMap
    (gCanonRight K Γ a b (c + d))
    (gCanonHphi5 K Γ a b c d hτ) n

theorem pcdHg2 :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (c + d)).carrier⦄,
      τ ∈ (Γ.D (c + d)).grading i →
      ∀ n : GQ2 K Γ a b (c + d) e,
        pcdGE2 K Γ a b c d e (τ • n)
          = ((sgn (gParity K Γ a (b + (c + d)) e * i) : ℤˣ) : ℤ) •
              (τ • pcdGE2 K Γ a b c d e n) :=
  fun _i _τ hτ n => GE2.comp_cslot_univ K Γ a b (c + d) e
    (gParity K Γ a (b + (c + d)) e)
    (gt2Canon K Γ a b (c + d) e
      (gTCanon K Γ a (b + (c + d)) e)).toLinearMap
    (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + (c + d)) e)
      (gParity K Γ a (b + (c + d)) e)
      (gTCanon_mem_gInterSpace K Γ a (b + (c + d)) e)) hτ n

theorem pcdHg3 :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (c + d)).carrier⦄,
      τ ∈ (Γ.D (c + d)).grading i →
      ∀ n : GQ3 K Γ a b (c + d) e,
        pcdGE3 K Γ a b c d e (τ • n)
          = ((sgn (gParity K Γ b (c + d) e * i) : ℤˣ) : ℤ) •
              (τ • pcdGE3 K Γ a b c d e n) :=
  fun _i _τ hτ n => GE3.comp_cslot_univ K Γ a b (c + d) e
    (gTCanon K Γ b (c + d) e).toLinearMap
    (gCanonRight K Γ b (c + d) e)
    (gCanonMidSlot K Γ b (c + d) e hτ) n

theorem pcdHg4 :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (c + d)).carrier⦄,
      τ ∈ (Γ.D (c + d)).grading i →
      ∀ n : GQ1 K Γ a b (c + d) e,
        pcdGE4 K Γ a b c d e (τ • n)
          = ((sgn (gParity K Γ (a + b) (c + d) e * i) : ℤˣ) : ℤ) •
              (τ • pcdGE4 K Γ a b c d e n) :=
  fun _i _τ hτ n => GE4.comp_cslot_univ K Γ a b (c + d) e
    (gParity K Γ (a + b) (c + d) e)
    (gTCanon K Γ (a + b) (c + d) e).toLinearMap
    (gCanonHphi4 K Γ a b (c + d) e) hτ
    (gCanonMidSlot K Γ (a + b) (c + d) e hτ) n

theorem pcdE19Map_hg :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (c + d)).carrier⦄,
      τ ∈ (Γ.D (c + d)).grading i →
      ∀ n : GQ5 K Γ a b (c + d) e,
        pcdE19Map K Γ a b c d e (τ • n)
          = ((sgn (gParity K Γ a b (c + d + e) * i) : ℤˣ) : ℤ) •
              (τ • pcdE19Map K Γ a b c d e n) := by
  intro i τ hτ n
  show gq4Close K Γ a b (c + d) e
      (GE5 K Γ a b (c + d) e
        (gParity K Γ a b (c + d + e))
        (gTCanon K Γ a b (c + d + e)).toLinearMap
        (gCanonHphi5 K Γ a b (c + d) e) (τ • n)) = _
  rw [GE5.comp_cslot_univ K Γ a b (c + d) e
      (gParity K Γ a b (c + d + e))
      (gTCanon K Γ a b (c + d + e)).toLinearMap
      (gCanonHphi5 K Γ a b (c + d) e) hτ,
    map_zsmul, GQ4Close.comp_cslot_univ K Γ a b (c + d) e]
  rfl

/-! ### Edge 5: the first shifted pentagon edge -/

private theorem E5M_pcd_mk
    (m : GQ5 K Γ a b c d)
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    E5M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (GQ5 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e)) m w)
      = pcdV5Pack K Γ a b c d e
          (gq4Close K Γ a b c d
            (GE5 K Γ a b c d (gParity K Γ a b (c + d))
              (gTCanon K Γ a b (c + d)).toLinearMap
              (gCanonHphi5 K Γ a b c d) m)) w :=
  E5M_mk K Γ a b c d e m w

private theorem pcdV5Pack_zsmul
    (z : ℤ) (m : GQ4 K Γ a b c d)
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    pcdV5Pack K Γ a b c d e (z • m) w
      = z • pcdV5Pack K Γ a b c d e m w := by
  unfold pcdV5Pack
  exact map_zsmul
    ((RelTensor.mk K (Γ.D (a + b + c + d)).carrier
      (GQ4 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))).flip w) z m

private theorem pcdE5GE5_gen {i j : ZMod 2}
    {t : FusionColumn (Γ.fuse a b)}
    (ht : t ∈ FusionColumn.grading (Γ.fuse a b) j)
    {u : FusionColumn (Γ.fuse c d)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse c d) i)
    (q : FusionColumn (Γ.fuse (a + b) (c + d))) :
    GE5 K Γ a b c d (gParity K Γ a b (c + d))
        (gTCanon K Γ a b (c + d)).toLinearMap
        (gCanonHphi5 K Γ a b c d)
        (GQ5.mk K Γ a b c d t (GBR.mk Γ (a + b) c d u q))
      = ((sgn (i * (gParity K Γ a b (c + d) + j)) : ℤˣ) : ℤ) •
          GQ4r.mk K Γ a b c d u
            (gTCanon K Γ a b (c + d) (GBL.mk Γ a b (c + d) t q)) :=
  GE5_mk_of_mem K Γ a b c d (gParity K Γ a b (c + d))
    (gTCanon K Γ a b (c + d)).toLinearMap
    (gCanonHphi5 K Γ a b c d) hu ht q

private theorem E5M_leaf_pcd {i j : ZMod 2}
    {t : FusionColumn (Γ.fuse a b)}
    (ht : t ∈ FusionColumn.grading (Γ.fuse a b) j)
    {u : FusionColumn (Γ.fuse c d)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse c d) i)
    (q : FusionColumn (Γ.fuse (a + b) (c + d)))
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    E5M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (GQ5 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GQ5.mk K Γ a b c d t (GBR.mk Γ (a + b) c d u q)) w)
      = ((sgn (i * (gParity K Γ a b (c + d) + j)) : ℤˣ) : ℤ) •
          pcdV5Pack K Γ a b c d e
            (gq4Close K Γ a b c d
              (GQ4r.mk K Γ a b c d u
                (gTCanon K Γ a b (c + d)
                  (GBL.mk Γ a b (c + d) t q)))) w := by
  rw [E5M_pcd_mk,
    pcdE5GE5_gen K Γ a b c d ht hu q,
    map_zsmul, pcdV5Pack_zsmul]

private theorem pcdGE1_gen
    (t : FusionColumn (Γ.fuse a b))
    (q : FusionColumn (Γ.fuse (a + b) (c + d)))
    (w : FusionColumn (Γ.fuse (a + b + (c + d)) e)) :
    pcdGE1 K Γ a b c d e
        (GQ1.mk K Γ a b (c + d) e (GBL.mk Γ a b (c + d) t q) w)
      = GQ2.mk K Γ a b (c + d) e
          (gTCanon K Γ a b (c + d) (GBL.mk Γ a b (c + d) t q)) w :=
  GE1_mk K Γ a b (c + d) e
    (gTCanon K Γ a b (c + d)).toLinearMap
    (gCanonRight K Γ a b (c + d)) (GBL.mk Γ a b (c + d) t q) w

private theorem recog_E5M_pcd_generator {i j : ZMod 2}
    {t : FusionColumn (Γ.fuse a b)}
    (ht : t ∈ FusionColumn.grading (Γ.fuse a b) j)
    {u : FusionColumn (Γ.fuse c d)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse c d) i)
    (q : FusionColumn (Γ.fuse (a + b) (c + d)))
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    omegaPcdV5 K Γ a b c d e
        (E5M K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
            (GQ5 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
            (GQ5.mk K Γ a b c d t (GBR.mk Γ (a + b) c d u q)) w))
      = smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
          (pcdGE1 K Γ a b c d e) (gParity K Γ a b (c + d))
          (pcdHg1 K Γ a b c d e)
          (omegaPcdV3 K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
              (GQ5 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
              (GQ5.mk K Γ a b c d t (GBR.mk Γ (a + b) c d u q)) w)) := by
  have sign_id : ∀ p i j : ZMod 2, i * (p + j) = i * j + p * i := by
    decide
  rw [E5M_leaf_pcd K Γ a b c d e ht hu q w,
    map_zsmul, omegaPcdV5_gq4Close_mk,
    omegaPcdV3_mk_of_mem K Γ a b c d e ht hu,
    map_zsmul,
    smap_mk_of_mem (Γ.D (c + d)).grading
      (FusionColumn.grading (Γ.fuse c d))
      (pcdGE1 K Γ a b c d e) (gParity K Γ a b (c + d))
      (pcdHg1 K Γ a b c d e) hu,
    pcdGE1_gen, smul_smul, ← Units.val_mul, ← sgn_add, sign_id]

/-- Edge 5 becomes `GE1` at `(a,b,c+d,e)` after extracting `F_{c,d}`. -/
theorem recog_E5M_pcd :
    (omegaPcdV5 K Γ a b c d e).toLinearMap ∘ₗ E5M K Γ a b c d e
      = smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
          (pcdGE1 K Γ a b c d e) (gParity K Γ a b (c + d))
          (pcdHg1 K Γ a b c d e)
          ∘ₗ (omegaPcdV3 K Γ a b c d e).toLinearMap := by
  refine RelTensor.hom_ext fun m w => ?_
  induction m using GQ5.induction_on_gen2 K Γ a b c d with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add m m' hm hm' => simp only [map_add, LinearMap.add_apply, hm, hm']
  | homog t u q ht hu =>
      exact recog_E5M_pcd_generator K Γ a b c d e ht hu q w

/-! ### Edge 7: the third shifted pentagon edge -/

private noncomputable def pcdV13OuterMap
    (x : FusionColumn (Γ.fuse a (b + c + d + e))) :
    GQ3 K Γ b c d e →ₗ[K] V13 K Γ a b c d e :=
  (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
    (GQ3 K Γ b c d e) (FusionColumn (Γ.fuse a (b + c + d + e)))).flip x

private theorem pcdV13OuterMap_apply
    (x : FusionColumn (Γ.fuse a (b + c + d + e)))
    (m : GQ3 K Γ b c d e) :
    pcdV13OuterMap K Γ a b c d e x m
      = RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (GQ3 K Γ b c d e) (FusionColumn (Γ.fuse a (b + c + d + e))) m x :=
  rfl

private noncomputable def pcdV13Gen
    (u : FusionColumn (Γ.fuse c d)) (m : GQ3Inner K Γ b c d e)
    (x : FusionColumn (Γ.fuse a (b + c + d + e))) :
    V13 K Γ a b c d e :=
  pcdV13OuterMap K Γ a b c d e x (GQ3.mk K Γ b c d e u m)

private theorem E7M_leaf_pcd_typed {i : ZMod 2}
    {u : FusionColumn (Γ.fuse c d)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse c d) i)
    (v : FusionColumn (Γ.fuse b (c + d)))
    (w : FusionColumn (Γ.fuse (b + c + d) e))
    (x : FusionColumn (Γ.fuse a (b + c + d + e))) :
    E7M K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (GQ2 K Γ b c d e) (FusionColumn (Γ.fuse a (b + c + d + e)))
          (GQ2.mk K Γ b c d e (GBR.mk Γ b c d u v) w) x)
      = ((sgn (gParity K Γ b (c + d) e * i) : ℤˣ) : ℤ) •
          pcdV13Gen K Γ a b c d e u
            (gt2Canon K Γ b c d e (gTCanon K Γ b (c + d) e)
              (RelTensor.mk K (Γ.D (b + c + d)).carrier
                (FusionColumn (Γ.fuse b (c + d)))
                (FusionColumn (Γ.fuse (b + c + d) e)) v w)) x := by
  have hGE2 := GE2_mk_of_mem K Γ b c d e (gParity K Γ b (c + d) e)
      (gt2Canon K Γ b c d e (gTCanon K Γ b (c + d) e)).toLinearMap
      (gt2Canon_bcSlot K Γ (gTCanon K Γ b (c + d) e)
        (gParity K Γ b (c + d) e)
        (gTCanon_mem_gInterSpace K Γ b (c + d) e)) hu v w
  calc
    E7M K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (GQ2 K Γ b c d e) (FusionColumn (Γ.fuse a (b + c + d + e)))
          (GQ2.mk K Γ b c d e (GBR.mk Γ b c d u v) w) x)
      = pcdV13OuterMap K Γ a b c d e x
          (GE2 K Γ b c d e (gParity K Γ b (c + d) e)
            (gt2Canon K Γ b c d e (gTCanon K Γ b (c + d) e)).toLinearMap
            (gt2Canon_bcSlot K Γ (gTCanon K Γ b (c + d) e)
              (gParity K Γ b (c + d) e)
              (gTCanon_mem_gInterSpace K Γ b (c + d) e))
            (GQ2.mk K Γ b c d e (GBR.mk Γ b c d u v) w)) := by
        rw [pcdV13OuterMap_apply]
        exact E7M_mk K Γ a b c d e
          (GQ2.mk K Γ b c d e (GBR.mk Γ b c d u v) w) x
    _ = pcdV13OuterMap K Γ a b c d e x
          (((sgn (gParity K Γ b (c + d) e * i) : ℤˣ) : ℤ) •
            GQ3.mk K Γ b c d e u
              (gt2Canon K Γ b c d e (gTCanon K Γ b (c + d) e)
                (RelTensor.mk K (Γ.D (b + c + d)).carrier
                  (FusionColumn (Γ.fuse b (c + d)))
                  (FusionColumn (Γ.fuse (b + c + d) e)) v w))) :=
        congrArg (pcdV13OuterMap K Γ a b c d e x) hGE2
    _ = ((sgn (gParity K Γ b (c + d) e * i) : ℤˣ) : ℤ) •
          pcdV13Gen K Γ a b c d e u
            (gt2Canon K Γ b c d e (gTCanon K Γ b (c + d) e)
              (RelTensor.mk K (Γ.D (b + c + d)).carrier
                (FusionColumn (Γ.fuse b (c + d)))
                (FusionColumn (Γ.fuse (b + c + d) e)) v w)) x := by
        rw [map_zsmul]
        rfl

private theorem omegaPcdV13_gen
    (u : FusionColumn (Γ.fuse c d)) (m : GQ3Inner K Γ b c d e)
    (x : FusionColumn (Γ.fuse a (b + c + d + e))) :
    omegaPcdV13 K Γ a b c d e (pcdV13Gen K Γ a b c d e u m x)
      = RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d)) (GQ4 K Γ a b (c + d) e) u
          (pcdV13InnerCast K Γ a b c d e
            (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
              (GQ3Inner K Γ b c d e)
              (FusionColumn (Γ.fuse a (b + c + d + e))) m x)) :=
  omegaPcdV13_core_mk K Γ a b c d e u m x

private noncomputable def pcdGQ3GenMap
    (v : FusionColumn (Γ.fuse b (c + d))) :
    GBR Γ a (b + (c + d)) e →ₗ[K] GQ3 K Γ a b (c + d) e :=
  GQ3.mk K Γ a b (c + d) e v

private noncomputable def pcdGQ3Gen
    (v : FusionColumn (Γ.fuse b (c + d)))
    (n : GBR Γ a (b + (c + d)) e) : GQ3 K Γ a b (c + d) e :=
  pcdGQ3GenMap K Γ a b c d e v n

private theorem pcdV11InnerCast_e7
    (v : FusionColumn (Γ.fuse b (c + d)))
    (w : FusionColumn (Γ.fuse (b + c + d) e))
    (x : FusionColumn (Γ.fuse a (b + c + d + e))) :
    pcdV11InnerCast K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d)).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e) v
          (GBR.mk Γ a (b + c + d) e w x))
      = pcdGQ3Gen K Γ a b c d e v
          (GBR.mk Γ a (b + (c + d)) e
            (gColumnCastFst K Γ e (add_assoc b c d) w)
            (fusionColumnCast K Γ a (pcdHeq b c d e) x)) := by
  rw [pcdV11InnerCast_mk, pcdGbrCastSnd_mk]
  rfl

private theorem pcdGE3_gen
    (v : FusionColumn (Γ.fuse b (c + d)))
    (w : FusionColumn (Γ.fuse (b + (c + d)) e))
    (x : FusionColumn (Γ.fuse a (b + (c + d) + e))) :
    pcdGE3 K Γ a b c d e
        (pcdGQ3Gen K Γ a b c d e v
          (GBR.mk Γ a (b + (c + d)) e w x))
      = GQ4.mk K Γ a b (c + d) e
          (gTCanon K Γ b (c + d) e (GBL.mk Γ b (c + d) e v w)) x := by
  exact GE3_mk K Γ a b (c + d) e
    (gTCanon K Γ b (c + d) e).toLinearMap
    (gCanonRight K Γ b (c + d) e) v w x

private theorem pcdV13InnerCast_e7
    (v : FusionColumn (Γ.fuse b (c + d)))
    (w : FusionColumn (Γ.fuse (b + c + d) e))
    (x : FusionColumn (Γ.fuse a (b + c + d + e))) :
    pcdV13InnerCast K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (GQ3Inner K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e)))
          (gt2Canon K Γ b c d e (gTCanon K Γ b (c + d) e)
            (RelTensor.mk K (Γ.D (b + c + d)).carrier
              (FusionColumn (Γ.fuse b (c + d)))
              (FusionColumn (Γ.fuse (b + c + d) e)) v w)) x)
      = GQ4.mk K Γ a b (c + d) e
          (gTCanon K Γ b (c + d) e
            (GBL.mk Γ b (c + d) e v
              (gColumnCastFst K Γ e (add_assoc b c d) w)))
          (fusionColumnCast K Γ a (pcdHeq b c d e) x) := by
  rw [gt2Canon_mk, pcdV13InnerCast_mk]

private theorem pcdE7Inner_bridge
    (v : FusionColumn (Γ.fuse b (c + d)))
    (w : FusionColumn (Γ.fuse (b + c + d) e))
    (x : FusionColumn (Γ.fuse a (b + c + d + e))) :
    pcdV13InnerCast K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (GQ3Inner K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e)))
          (gt2Canon K Γ b c d e (gTCanon K Γ b (c + d) e)
            (RelTensor.mk K (Γ.D (b + c + d)).carrier
              (FusionColumn (Γ.fuse b (c + d)))
              (FusionColumn (Γ.fuse (b + c + d) e)) v w)) x)
      = pcdGE3 K Γ a b c d e
          (pcdV11InnerCast K Γ a b c d e
            (RelTensor.mk K (Γ.D (b + c + d)).carrier
              (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e) v
              (GBR.mk Γ a (b + c + d) e w x))) := by
  rw [pcdV13InnerCast_e7, pcdV11InnerCast_e7, pcdGE3_gen]

private theorem recog_E7M_pcd_generator {i : ZMod 2}
    {u : FusionColumn (Γ.fuse c d)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse c d) i)
    (v : FusionColumn (Γ.fuse b (c + d)))
    (w : FusionColumn (Γ.fuse (b + c + d) e))
    (x : FusionColumn (Γ.fuse a (b + c + d + e))) :
    omegaPcdV13 K Γ a b c d e
        (E7M K Γ a b c d e
          (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
            (GQ2 K Γ b c d e) (FusionColumn (Γ.fuse a (b + c + d + e)))
            (GQ2.mk K Γ b c d e (GBR.mk Γ b c d u v) w) x))
      = smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
          (pcdGE3 K Γ a b c d e) (gParity K Γ b (c + d) e)
          (pcdHg3 K Γ a b c d e)
          (omegaPcdV11 K Γ a b c d e
            (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
              (GQ2 K Γ b c d e) (FusionColumn (Γ.fuse a (b + c + d + e)))
              (GQ2.mk K Γ b c d e (GBR.mk Γ b c d u v) w) x)) := by
  rw [E7M_leaf_pcd_typed K Γ a b c d e hu v w x,
    map_zsmul, omegaPcdV13_gen, omegaPcdV11_core_mk,
    smap_mk_of_mem (Γ.D (c + d)).grading
      (FusionColumn.grading (Γ.fuse c d))
      (pcdGE3 K Γ a b c d e) (gParity K Γ b (c + d) e)
      (pcdHg3 K Γ a b c d e) hu,
    pcdE7Inner_bridge]

/-- Edge 7 becomes `GE3` at `(a,b,c+d,e)` after extracting `F_{c,d}`. -/
theorem recog_E7M_pcd :
    (omegaPcdV13 K Γ a b c d e).toLinearMap ∘ₗ E7M K Γ a b c d e
      = smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
          (pcdGE3 K Γ a b c d e) (gParity K Γ b (c + d) e)
          (pcdHg3 K Γ a b c d e)
          ∘ₗ (omegaPcdV11 K Γ a b c d e).toLinearMap := by
  refine RelTensor.hom_ext fun m x => ?_
  induction m using GQ2.induction_on_gen K Γ b c d e with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add m m' hm hm' => simp only [map_add, LinearMap.add_apply, hm, hm']
  | homog u v w hu =>
      exact recog_E7M_pcd_generator K Γ a b c d e hu v w x

/-! ### Edge 18: the second shifted pentagon edge -/

/-- The cast introduced by the `V5` extraction is exactly the cast
consumed by `gt2Canon`.  What remains is naturality of the canonical
triple map under `b+c+d = b+(c+d)`. -/
private theorem pcdE18Canon_bridge
    (x : FusionColumn (Γ.fuse a (b + c + d)))
    (w : FusionColumn (Γ.fuse (a + (b + c + d)) e)) :
    gt2Canon K Γ a b (c + d) e
        (gTCanon K Γ a (b + (c + d)) e)
        (RelTensor.mk K (Γ.D (a + b + (c + d))).carrier
          (FusionColumn (Γ.fuse a (b + (c + d))))
          (FusionColumn (Γ.fuse (a + b + (c + d)) e))
          (fusionColumnCast K Γ a (add_assoc b c d) x)
          (gColumnCastFst K Γ e (pcdV5TotalHeq a b c d)
            (gColumnCastFst K Γ e
              (congrArg (a + ·) (add_assoc b c d)) w)))
      = pcdGbrCastSnd K Γ a e (add_assoc b c d)
          (gTCanon K Γ a (b + c + d) e
            (GBL.mk Γ a (b + c + d) e x w)) := by
  rw [gt2Canon_mk, pcdGCanonCastSnd, pcdGblCastSnd_mk,
    gColumnCastFst_trans]
  rfl

private theorem pcdGE2_gen {j : ZMod 2}
    {v : FusionColumn (Γ.fuse b (c + d))}
    (hv : v ∈ FusionColumn.grading (Γ.fuse b (c + d)) j)
    (x : FusionColumn (Γ.fuse a (b + (c + d))))
    (w : FusionColumn (Γ.fuse (a + b + (c + d)) e)) :
    pcdGE2 K Γ a b c d e
        (GQ2.mk K Γ a b (c + d) e
          (GBR.mk Γ a b (c + d) v x) w)
      = ((sgn (gParity K Γ a (b + (c + d)) e * j) : ℤˣ) : ℤ) •
          GQ3.mk K Γ a b (c + d) e v
            (gt2Canon K Γ a b (c + d) e
              (gTCanon K Γ a (b + (c + d)) e)
              (RelTensor.mk K (Γ.D (a + b + (c + d))).carrier
                (FusionColumn (Γ.fuse a (b + (c + d))))
                (FusionColumn (Γ.fuse (a + b + (c + d)) e)) x w)) := by
  exact GE2_mk_of_mem K Γ a b (c + d) e
    (gParity K Γ a (b + (c + d)) e)
    (gt2Canon K Γ a b (c + d) e
      (gTCanon K Γ a (b + (c + d)) e)).toLinearMap
    (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + (c + d)) e)
      (gParity K Γ a (b + (c + d)) e)
      (gTCanon_mem_gInterSpace K Γ a (b + (c + d)) e)) hv x w

/-- On the residual factor, the extracted edge is the canonical second
pentagon edge.  Its only sign is the degree of the exposed
`F_{b,c+d}` generator. -/
private theorem pcdE18Inner_bridge {j : ZMod 2}
    {v : FusionColumn (Γ.fuse b (c + d))}
    (hv : v ∈ FusionColumn.grading (Γ.fuse b (c + d)) j)
    (x : FusionColumn (Γ.fuse a (b + c + d)))
    (w : FusionColumn (Γ.fuse (a + (b + c + d)) e)) :
    pcdGE2 K Γ a b c d e
        (pcdV5InnerCast K Γ a b c d e
          (RelTensor.mk K (Γ.D (b + c + d)).carrier
            (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + c + d) e)
            v (GBL.mk Γ a (b + c + d) e x w)))
      = ((sgn (gParity K Γ a (b + (c + d)) e * j) : ℤˣ) : ℤ) •
          pcdV11InnerCast K Γ a b c d e
            (RelTensor.mk K (Γ.D (b + c + d)).carrier
              (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e)
              v (gTCanon K Γ a (b + c + d) e
                (GBL.mk Γ a (b + c + d) e x w))) := by
  rw [pcdV5InnerCast_mk, pcdGE2_gen K Γ a b c d e hv,
    pcdV11InnerCast_mk, pcdE18Canon_bridge]

private theorem recog_E18M_pcd_generator {i j : ZMod 2}
    {u : FusionColumn (Γ.fuse c d)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse c d) i)
    {v : FusionColumn (Γ.fuse b (c + d))}
    (hv : v ∈ FusionColumn.grading (Γ.fuse b (c + d)) j)
    (x : FusionColumn (Γ.fuse a (b + c + d)))
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    omegaPcdV11 K Γ a b c d e
        (E18M K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
            (GQ4 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
            (GQ4.mk K Γ a b c d (GBR.mk Γ b c d u v) x) w))
      = smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
          (pcdGE2 K Γ a b c d e) (gParity K Γ a (b + (c + d)) e)
          (pcdHg2 K Γ a b c d e)
          (omegaPcdV5 K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
              (GQ4 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
              (GQ4.mk K Γ a b c d (GBR.mk Γ b c d u v) x) w)) := by
  have hp : gParity K Γ a (b + c + d) e
      = gParity K Γ a (b + (c + d)) e :=
    congrArg (fun q => gParity K Γ a q e) (add_assoc b c d)
  have sign_id : ∀ p i j : ZMod 2, p * (i + j) = p * i + p * j := by
    decide
  rw [E18M_leaf_pcd K Γ a b c d e hu hv x w,
    map_zsmul, omegaPcdV11_gV11Assoc_symm_mk,
    omegaPcdV5_core_mk,
    smap_mk_of_mem (Γ.D (c + d)).grading
      (FusionColumn.grading (Γ.fuse c d))
      (pcdGE2 K Γ a b c d e) (gParity K Γ a (b + (c + d)) e)
      (pcdHg2 K Γ a b c d e) hu,
    pcdE18Inner_bridge K Γ a b c d e hv,
    map_zsmul, smul_smul, ← Units.val_mul, ← sgn_add, hp, sign_id]

@[elab_as_elim]
private theorem pcdGQ4_induction_on
    {motive : GQ4 K Γ a b c d → Prop} (m : GQ4 K Γ a b c d)
    (zero : motive 0)
    (mk : ∀ (n : GBR Γ b c d) (x : FusionColumn (Γ.fuse a (b + c + d))),
      motive (GQ4.mk K Γ a b c d n x))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive m :=
  RelTensor.induction_on K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
    (FusionColumn (Γ.fuse a (b + c + d))) m zero mk add

/-- Edge 18 becomes `GE2` at `(a,b,c+d,e)` after extracting `F_{c,d}`. -/
theorem recog_E18M_pcd :
    (omegaPcdV11 K Γ a b c d e).toLinearMap ∘ₗ E18M K Γ a b c d e
      = smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
          (pcdGE2 K Γ a b c d e) (gParity K Γ a (b + (c + d)) e)
          (pcdHg2 K Γ a b c d e)
          ∘ₗ (omegaPcdV5 K Γ a b c d e).toLinearMap := by
  refine RelTensor.hom_ext fun q w => ?_
  induction q using pcdGQ4_induction_on K Γ a b c d with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add q q' hq hq' => simp only [map_add, LinearMap.add_apply, hq, hq']
  | mk n x =>
      induction n using GBR.induction_on_gen2 K Γ b c d with
      | zero => simp only [map_zero, LinearMap.zero_apply]
      | add n n' hn hn' => simp only [map_add, LinearMap.add_apply, hn, hn']
      | homog u v hu hv =>
          exact recog_E18M_pcd_generator K Γ a b c d e hu hv x w

/-! ### Edge 11: the fourth shifted pentagon edge -/

private theorem pcdGE4_gen {j : ZMod 2}
    {t : FusionColumn (Γ.fuse a b)}
    (ht : t ∈ FusionColumn.grading (Γ.fuse a b) j)
    (q : FusionColumn (Γ.fuse (a + b) (c + d)))
    (w : FusionColumn (Γ.fuse (a + b + (c + d)) e)) :
    pcdGE4 K Γ a b c d e
        (GQ1.mk K Γ a b (c + d) e
          (GBL.mk Γ a b (c + d) t q) w)
      = ((sgn (gParity K Γ (a + b) (c + d) e * j) : ℤˣ) : ℤ) •
          GQ5.mk K Γ a b (c + d) e t
            (gTCanon K Γ (a + b) (c + d) e
              (GBL.mk Γ (a + b) (c + d) e q w)) := by
  exact GE4_mk_of_mem K Γ a b (c + d) e
    (gParity K Γ (a + b) (c + d) e)
    (gTCanon K Γ (a + b) (c + d) e).toLinearMap
    (gCanonHphi4 K Γ a b (c + d) e) ht q w

private noncomputable def pcdE11Gt2 :
    GQ2rInner K Γ (a + b) c d e ≃ₗ[K] GBR Γ (a + b) (c + d) e :=
  gt2Canon K Γ (a + b) c d e
    (gTCanon K Γ (a + b) (c + d) e)

private theorem pcdE11Gt2_mk
    (q : FusionColumn (Γ.fuse (a + b) (c + d)))
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    pcdE11Gt2 K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (FusionColumn (Γ.fuse (a + b) (c + d)))
          (FusionColumn (Γ.fuse (a + b + c + d) e)) q w)
      = gTCanon K Γ (a + b) (c + d) e
          (GBL.mk Γ (a + b) (c + d) e q
            (gColumnCastFst K Γ e (add_assoc (a + b) c d) w)) :=
  gt2Canon_mk K Γ (a + b) c d e
    (gTCanon K Γ (a + b) (c + d) e) q w

private noncomputable def pcdV8Gen
    (t : FusionColumn (Γ.fuse a b)) (n : V8Inner K Γ a b c d e) :
    V8 K Γ a b c d e :=
  RelTensor.mk K (Γ.D (a + b)).carrier
    (FusionColumn (Γ.fuse a b)) (V8Inner K Γ a b c d e) t n

private theorem E11M_leaf_pcd_typed {i j : ZMod 2}
    {t : FusionColumn (Γ.fuse a b)}
    (ht : t ∈ FusionColumn.grading (Γ.fuse a b) j)
    {u : FusionColumn (Γ.fuse c d)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse c d) i)
    (q : FusionColumn (Γ.fuse (a + b) (c + d)))
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    E11M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (GQ5 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GQ5.mk K Γ a b c d t (GBR.mk Γ (a + b) c d u q)) w)
      = ((sgn (gParity K Γ (a + b) (c + d) e * (j + i)) : ℤˣ) : ℤ) •
          pcdV8Gen K Γ a b c d e t
            (gE11GBRAssoc K Γ a b c d e
              (RelTensor.mk K (Γ.D (c + d)).carrier
                (FusionColumn (Γ.fuse c d)) (GBR Γ (a + b) (c + d) e) u
                (pcdE11Gt2 K Γ a b c d e
                  (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                    (FusionColumn (Γ.fuse (a + b) (c + d)))
                    (FusionColumn (Γ.fuse (a + b + c + d) e)) q w)))) := by
  exact E11M_leaf K Γ a b c d e ht hu q w

private theorem omegaPcdV8_e11_gen {i j : ZMod 2}
    {t : FusionColumn (Γ.fuse a b)}
    (ht : t ∈ FusionColumn.grading (Γ.fuse a b) j)
    {u : FusionColumn (Γ.fuse c d)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse c d) i)
    (n : GBR Γ (a + b) (c + d) e) :
    omegaPcdV8 K Γ a b c d e
        (pcdV8Gen K Γ a b c d e t
          (gE11GBRAssoc K Γ a b c d e
            (RelTensor.mk K (Γ.D (c + d)).carrier
              (FusionColumn (Γ.fuse c d)) (GBR Γ (a + b) (c + d) e) u n)))
      = ((sgn (i * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (c + d)).carrier
            (FusionColumn (Γ.fuse c d)) (GQ5 K Γ a b (c + d) e) u
            (GQ5.mk K Γ a b (c + d) e t n) := by
  exact omegaPcdV8_gE11Assoc_mk_of_mem K Γ a b c d e ht hu n

private theorem recog_E11M_pcd_generator {i j : ZMod 2}
    {t : FusionColumn (Γ.fuse a b)}
    (ht : t ∈ FusionColumn.grading (Γ.fuse a b) j)
    {u : FusionColumn (Γ.fuse c d)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse c d) i)
    (q : FusionColumn (Γ.fuse (a + b) (c + d)))
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    omegaPcdV8 K Γ a b c d e
        (E11M K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
            (GQ5 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
            (GQ5.mk K Γ a b c d t (GBR.mk Γ (a + b) c d u q)) w))
      = smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
          (pcdGE4 K Γ a b c d e) (gParity K Γ (a + b) (c + d) e)
          (pcdHg4 K Γ a b c d e)
          (omegaPcdV3 K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
              (GQ5 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
              (GQ5.mk K Γ a b c d t (GBR.mk Γ (a + b) c d u q)) w)) := by
  have sign_id : ∀ p i j : ZMod 2,
      p * (j + i) + i * j = i * j + p * i + p * j := by
    decide
  rw [E11M_leaf_pcd_typed K Γ a b c d e ht hu q w,
    map_zsmul, omegaPcdV8_e11_gen K Γ a b c d e ht hu,
    omegaPcdV3_mk_of_mem K Γ a b c d e ht hu,
    map_zsmul,
    smap_mk_of_mem (Γ.D (c + d)).grading
      (FusionColumn.grading (Γ.fuse c d))
      (pcdGE4 K Γ a b c d e) (gParity K Γ (a + b) (c + d) e)
      (pcdHg4 K Γ a b c d e) hu,
    pcdGE4_gen K Γ a b c d e ht,
    map_zsmul, pcdE11Gt2_mk,
    smul_smul, smul_smul, ← Units.val_mul, ← sgn_add,
    ← Units.val_mul, ← sgn_add, sign_id,
    smul_smul, ← Units.val_mul, ← sgn_add]

/-- Edge 11 becomes `GE4` at `(a,b,c+d,e)` after extracting `F_{c,d}`. -/
theorem recog_E11M_pcd :
    (omegaPcdV8 K Γ a b c d e).toLinearMap ∘ₗ E11M K Γ a b c d e
      = smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
          (pcdGE4 K Γ a b c d e) (gParity K Γ (a + b) (c + d) e)
          (pcdHg4 K Γ a b c d e)
          ∘ₗ (omegaPcdV3 K Γ a b c d e).toLinearMap := by
  refine RelTensor.hom_ext fun m w => ?_
  induction m using GQ5.induction_on_gen2 K Γ a b c d with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add m m' hm hm' => simp only [map_add, LinearMap.add_apply, hm, hm']
  | homog t u q ht hu =>
      exact recog_E11M_pcd_generator K Γ a b c d e ht hu q w

/-! ### Edge 19: the fifth shifted pentagon edge -/

private theorem pcdV13Regroup_mk
    (s : FusionColumn (Γ.fuse (c + d) e))
    (n : FusionColumn (Γ.fuse b (c + d + e)))
    (x : FusionColumn (Γ.fuse a (b + c + d + e))) :
    gV13Regroup K Γ a b c d e
        (RelTensor.mk K (Γ.D (c + d + e)).carrier
          (FusionColumn (Γ.fuse (c + d) e))
          (RelTensor K (Γ.D (b + c + d + e)).carrier
            (FusionColumn (Γ.fuse b (c + d + e)))
            (FusionColumn (Γ.fuse a (b + c + d + e)))) s
          (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
            (FusionColumn (Γ.fuse b (c + d + e)))
            (FusionColumn (Γ.fuse a (b + c + d + e))) n x))
      = RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (GQ3Inner K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e)))
          (GBR.mk Γ b (c + d) e s n) x :=
  RelTensor.assoc_symm_mk K (Γ.D (c + d + e)).carrier
    (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
    (FusionColumn (Γ.fuse b (c + d + e)))
    (FusionColumn (Γ.fuse a (b + c + d + e))) s n x

private theorem pcdGq4Close_gen
    (s : FusionColumn (Γ.fuse (c + d) e))
    (n : FusionColumn (Γ.fuse b (c + d + e)))
    (x : FusionColumn (Γ.fuse a (b + (c + d + e)))) :
    gq4Close K Γ a b (c + d) e
        (GQ4r.mk K Γ a b (c + d) e s
          (GBR.mk Γ a b (c + d + e) n x))
      = GQ4.mk K Γ a b (c + d) e
          (GBR.mk Γ b (c + d) e s n)
          (fusionColumnCast K Γ a (add_assoc b (c + d) e).symm x) := by
  exact gq4Close_mk K Γ a b (c + d) e s n x

private theorem pcdE19Close_bridge_mk
    (s : FusionColumn (Γ.fuse (c + d) e))
    (n : FusionColumn (Γ.fuse b (c + d + e)))
    (x : FusionColumn (Γ.fuse a (b + (c + d + e)))) :
    pcdV13InnerCast K Γ a b c d e
        (gV13Regroup K Γ a b c d e
          (RelTensor.mk K (Γ.D (c + d + e)).carrier
            (FusionColumn (Γ.fuse (c + d) e))
            (RelTensor K (Γ.D (b + c + d + e)).carrier
              (FusionColumn (Γ.fuse b (c + d + e)))
              (FusionColumn (Γ.fuse a (b + c + d + e)))) s
            ((gq3rCast K Γ a b c d e).symm
              (GBR.mk Γ a b (c + d + e) n x))))
      = gq4Close K Γ a b (c + d) e
          (GQ4r.mk K Γ a b (c + d) e s
            (GBR.mk Γ a b (c + d + e) n x)) := by
  rw [gq3rCast_symm_mk, pcdV13Regroup_mk,
    pcdV13InnerCast_mk, pcdGq4Close_gen,
    ← pcdFusionColumnCast_symm_eq K Γ a (add_assoc_four b c d e),
    pcdFusionColumnCast_trans]

private theorem pcdE19Close_bridge
    (s : FusionColumn (Γ.fuse (c + d) e))
    (n : GBR Γ a b (c + d + e)) :
    pcdV13InnerCast K Γ a b c d e
        (gV13Regroup K Γ a b c d e
          (RelTensor.mk K (Γ.D (c + d + e)).carrier
            (FusionColumn (Γ.fuse (c + d) e))
            (RelTensor K (Γ.D (b + c + d + e)).carrier
              (FusionColumn (Γ.fuse b (c + d + e)))
              (FusionColumn (Γ.fuse a (b + c + d + e)))) s
            ((gq3rCast K Γ a b c d e).symm n)))
      = gq4Close K Γ a b (c + d) e
          (GQ4r.mk K Γ a b (c + d) e s n) := by
  induction n using GBR.induction_on K Γ a b (c + d + e) with
  | zero => simp only [map_zero]
  | add n n' hn hn' => simp only [map_add, hn, hn']
  | mk n x => exact pcdE19Close_bridge_mk K Γ a b c d e s n x

private theorem pcdGE5_gen {j js : ZMod 2}
    {t : FusionColumn (Γ.fuse a b)}
    (ht : t ∈ FusionColumn.grading (Γ.fuse a b) j)
    {s : FusionColumn (Γ.fuse (c + d) e)}
    (hs : s ∈ FusionColumn.grading (Γ.fuse (c + d) e) js)
    (p : FusionColumn (Γ.fuse (a + b) (c + d + e))) :
    GE5 K Γ a b (c + d) e
        (gParity K Γ a b (c + d + e))
        (gTCanon K Γ a b (c + d + e)).toLinearMap
        (gCanonHphi5 K Γ a b (c + d) e)
        (GQ5.mk K Γ a b (c + d) e t
          (GBR.mk Γ (a + b) (c + d) e s p))
      = ((sgn (js * (gParity K Γ a b (c + d + e) + j)) : ℤˣ) : ℤ) •
          GQ4r.mk K Γ a b (c + d) e s
            (gTCanon K Γ a b (c + d + e)
              (GBL.mk Γ a b (c + d + e) t p)) := by
  exact GE5_mk_of_mem K Γ a b (c + d) e
    (gParity K Γ a b (c + d + e))
    (gTCanon K Γ a b (c + d + e)).toLinearMap
    (gCanonHphi5 K Γ a b (c + d) e) hs ht p

private theorem pcdE19Map_gen {j js : ZMod 2}
    {t : FusionColumn (Γ.fuse a b)}
    (ht : t ∈ FusionColumn.grading (Γ.fuse a b) j)
    {s : FusionColumn (Γ.fuse (c + d) e)}
    (hs : s ∈ FusionColumn.grading (Γ.fuse (c + d) e) js)
    (p : FusionColumn (Γ.fuse (a + b) (c + d + e))) :
    pcdE19Map K Γ a b c d e
        (GQ5.mk K Γ a b (c + d) e t
          (GBR.mk Γ (a + b) (c + d) e s p))
      = ((sgn (js * (gParity K Γ a b (c + d + e) + j)) : ℤˣ) : ℤ) •
          gq4Close K Γ a b (c + d) e
            (GQ4r.mk K Γ a b (c + d) e s
              (gTCanon K Γ a b (c + d + e)
                (GBL.mk Γ a b (c + d + e) t p))) := by
  show gq4Close K Γ a b (c + d) e
      (GE5 K Γ a b (c + d) e
        (gParity K Γ a b (c + d + e))
        (gTCanon K Γ a b (c + d + e)).toLinearMap
        (gCanonHphi5 K Γ a b (c + d) e)
        (GQ5.mk K Γ a b (c + d) e t
          (GBR.mk Γ (a + b) (c + d) e s p))) = _
  rw [pcdGE5_gen K Γ a b c d e ht hs, map_zsmul]

private noncomputable def pcdV13ClosedGen
    (r : FusionColumn (Γ.fuse c d))
    (n : RelTensor K (Γ.D (b + c + d + e)).carrier
      (GQ3Inner K Γ b c d e) (FusionColumn (Γ.fuse a (b + c + d + e)))) :
    V13 K Γ a b c d e :=
  gV13StepB K Γ a b c d e
    (RelTensor.mk K (Γ.D (c + d)).carrier
      (FusionColumn (Γ.fuse c d))
      (RelTensor K (Γ.D (b + c + d + e)).carrier
        (GQ3Inner K Γ b c d e) (FusionColumn (Γ.fuse a (b + c + d + e)))) r n)

private theorem omegaPcdV13_closed_gen
    (r : FusionColumn (Γ.fuse c d))
    (n : RelTensor K (Γ.D (b + c + d + e)).carrier
      (GQ3Inner K Γ b c d e) (FusionColumn (Γ.fuse a (b + c + d + e)))) :
    omegaPcdV13 K Γ a b c d e (pcdV13ClosedGen K Γ a b c d e r n)
      = RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d)) (GQ4 K Γ a b (c + d) e) r
          (pcdV13InnerCast K Γ a b c d e n) := by
  exact omegaPcdV13_gV13StepB_mk K Γ a b c d e r n

private theorem E19M_leaf_pcd_typed {j i js : ZMod 2}
    {t : FusionColumn (Γ.fuse a b)}
    (ht : t ∈ FusionColumn.grading (Γ.fuse a b) j)
    {r : FusionColumn (Γ.fuse c d)}
    (hr : r ∈ FusionColumn.grading (Γ.fuse c d) i)
    {s : FusionColumn (Γ.fuse (c + d) e)}
    (hs : s ∈ FusionColumn.grading (Γ.fuse (c + d) e) js)
    (p : FusionColumn (Γ.fuse (a + b) (c + d + e))) :
    E19M K Γ a b c d e
        (pcdV8Gen K Γ a b c d e t
          (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
            (FusionColumn (Γ.fuse (a + b) (c + d + e)))
            (GBL.mk Γ c d e r s) p))
      = ((sgn ((i + js) * (j + gParity K Γ a b (c + d + e))) : ℤˣ) : ℤ) •
          pcdV13ClosedGen K Γ a b c d e r
            (gV13Regroup K Γ a b c d e
              (RelTensor.mk K (Γ.D (c + d + e)).carrier
                (FusionColumn (Γ.fuse (c + d) e))
                (RelTensor K (Γ.D (b + c + d + e)).carrier
                  (FusionColumn (Γ.fuse b (c + d + e)))
                  (FusionColumn (Γ.fuse a (b + c + d + e)))) s
                ((gq3rCast K Γ a b c d e).symm
                  (gTCanon K Γ a b (c + d + e)
                    (GBL.mk Γ a b (c + d + e) t p))))) := by
  exact E19M_leaf K Γ a b c d e ht hr hs p

private theorem omegaPcdV8_e19_gen {j i : ZMod 2}
    {t : FusionColumn (Γ.fuse a b)}
    (ht : t ∈ FusionColumn.grading (Γ.fuse a b) j)
    {r : FusionColumn (Γ.fuse c d)}
    (hr : r ∈ FusionColumn.grading (Γ.fuse c d) i)
    (s : FusionColumn (Γ.fuse (c + d) e))
    (p : FusionColumn (Γ.fuse (a + b) (c + d + e))) :
    omegaPcdV8 K Γ a b c d e
        (pcdV8Gen K Γ a b c d e t
          (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
            (FusionColumn (Γ.fuse (a + b) (c + d + e)))
            (GBL.mk Γ c d e r s) p))
      = ((sgn (i * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (c + d)).carrier
            (FusionColumn (Γ.fuse c d)) (GQ5 K Γ a b (c + d) e) r
            (GQ5.mk K Γ a b (c + d) e t
              (GBR.mk Γ (a + b) (c + d) e s p)) := by
  exact omegaPcdV8_mk_of_mem K Γ a b c d e ht hr s p

private theorem recog_E19M_pcd_generator {j i js : ZMod 2}
    {t : FusionColumn (Γ.fuse a b)}
    (ht : t ∈ FusionColumn.grading (Γ.fuse a b) j)
    {r : FusionColumn (Γ.fuse c d)}
    (hr : r ∈ FusionColumn.grading (Γ.fuse c d) i)
    {s : FusionColumn (Γ.fuse (c + d) e)}
    (hs : s ∈ FusionColumn.grading (Γ.fuse (c + d) e) js)
    (p : FusionColumn (Γ.fuse (a + b) (c + d + e))) :
    omegaPcdV13 K Γ a b c d e
        (E19M K Γ a b c d e
          (pcdV8Gen K Γ a b c d e t
            (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
              (FusionColumn (Γ.fuse (a + b) (c + d + e)))
              (GBL.mk Γ c d e r s) p)))
      = smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
          (pcdE19Map K Γ a b c d e) (gParity K Γ a b (c + d + e))
          (pcdE19Map_hg K Γ a b c d e)
          (omegaPcdV8 K Γ a b c d e
            (pcdV8Gen K Γ a b c d e t
              (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
                (FusionColumn (Γ.fuse (a + b) (c + d + e)))
                (GBL.mk Γ c d e r s) p))) := by
  have sign_id : ∀ p i j k : ZMod 2,
      (i + k) * (j + p) = i * j + p * i + k * (p + j) := by
    decide
  rw [E19M_leaf_pcd_typed K Γ a b c d e ht hr hs p,
    map_zsmul, omegaPcdV13_closed_gen,
    pcdE19Close_bridge,
    omegaPcdV8_e19_gen K Γ a b c d e ht hr,
    map_zsmul,
    smap_mk_of_mem (Γ.D (c + d)).grading
      (FusionColumn.grading (Γ.fuse c d))
      (pcdE19Map K Γ a b c d e) (gParity K Γ a b (c + d + e))
      (pcdE19Map_hg K Γ a b c d e) hr,
    pcdE19Map_gen K Γ a b c d e ht hs,
    map_zsmul, smul_smul, smul_smul,
    ← Units.val_mul, ← sgn_add, ← Units.val_mul, ← sgn_add,
    sign_id]

@[elab_as_elim]
private theorem pcdV8_induction_on_left_homog
    {motive : V8 K Γ a b c d e → Prop} (z : V8 K Γ a b c d e)
    (zero : motive 0)
    (homog : ∀ (j : ZMod 2) (t : FusionColumn (Γ.fuse a b))
      (n : V8Inner K Γ a b c d e),
      t ∈ FusionColumn.grading (Γ.fuse a b) j →
        motive (pcdV8Gen K Γ a b c d e t n))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  PentagonB.RelTensor.induction_on_left_homog K
    (FusionColumn.grading (Γ.fuse a b)) z zero homog add

private noncomputable def pcdV8OuterMap
    (t : FusionColumn (Γ.fuse a b)) :
    V8Inner K Γ a b c d e →ₗ[K] V8 K Γ a b c d e :=
  RelTensor.mk K (Γ.D (a + b)).carrier
    (FusionColumn (Γ.fuse a b)) (V8Inner K Γ a b c d e) t

private theorem pcdV8OuterMap_apply
    (t : FusionColumn (Γ.fuse a b)) (n : V8Inner K Γ a b c d e) :
    pcdV8OuterMap K Γ a b c d e t n = pcdV8Gen K Γ a b c d e t n :=
  rfl

private noncomputable def pcdE19LhsInner
    (t : FusionColumn (Γ.fuse a b)) :
    V8Inner K Γ a b c d e →ₗ[K]
      RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
        (GQ4 K Γ a b (c + d) e) :=
  (omegaPcdV13 K Γ a b c d e).toLinearMap.comp
    ((E19M K Γ a b c d e).comp (pcdV8OuterMap K Γ a b c d e t))

private noncomputable def pcdE19RhsInner
    (t : FusionColumn (Γ.fuse a b)) :
    V8Inner K Γ a b c d e →ₗ[K]
      RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
        (GQ4 K Γ a b (c + d) e) :=
  (smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
    (pcdE19Map K Γ a b c d e) (gParity K Γ a b (c + d + e))
    (pcdE19Map_hg K Γ a b c d e)).comp
      ((omegaPcdV8 K Γ a b c d e).toLinearMap.comp
        (pcdV8OuterMap K Γ a b c d e t))

private theorem pcdE19LhsInner_apply
    (t : FusionColumn (Γ.fuse a b)) (n : V8Inner K Γ a b c d e) :
    pcdE19LhsInner K Γ a b c d e t n
      = omegaPcdV13 K Γ a b c d e
          (E19M K Γ a b c d e (pcdV8Gen K Γ a b c d e t n)) :=
  rfl

private theorem pcdE19RhsInner_apply
    (t : FusionColumn (Γ.fuse a b)) (n : V8Inner K Γ a b c d e) :
    pcdE19RhsInner K Γ a b c d e t n
      = smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
          (pcdE19Map K Γ a b c d e) (gParity K Γ a b (c + d + e))
          (pcdE19Map_hg K Γ a b c d e)
          (omegaPcdV8 K Γ a b c d e (pcdV8Gen K Γ a b c d e t n)) :=
  rfl

private noncomputable def pcdE19LhsInnerRaw
    (t : FusionColumn (Γ.fuse a b)) :
    RelTensor K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
        (FusionColumn (Γ.fuse (a + b) (c + d + e))) →ₗ[K]
      RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
        (GQ4 K Γ a b (c + d) e) where
  toFun := fun n => pcdE19LhsInner K Γ a b c d e t n
  map_add' := (pcdE19LhsInner K Γ a b c d e t).map_add
  map_smul' := (pcdE19LhsInner K Γ a b c d e t).map_smul

private noncomputable def pcdE19RhsInnerRaw
    (t : FusionColumn (Γ.fuse a b)) :
    RelTensor K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
        (FusionColumn (Γ.fuse (a + b) (c + d + e))) →ₗ[K]
      RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
        (GQ4 K Γ a b (c + d) e) where
  toFun := fun n => pcdE19RhsInner K Γ a b c d e t n
  map_add' := (pcdE19RhsInner K Γ a b c d e t).map_add
  map_smul' := (pcdE19RhsInner K Γ a b c d e t).map_smul

private theorem pcdE19Inner_maps_eq {j : ZMod 2}
    {t : FusionColumn (Γ.fuse a b)}
    (ht : t ∈ FusionColumn.grading (Γ.fuse a b) j) :
    pcdE19LhsInnerRaw K Γ a b c d e t
      = pcdE19RhsInnerRaw K Γ a b c d e t := by
  refine RelTensor.hom_ext fun m p => ?_
  induction m using GBL.induction_on_gen2 K Γ c d e with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add m m' hm hm' => simp only [map_add, LinearMap.add_apply, hm, hm']
  | homog r s hr hs =>
      change pcdE19LhsInner K Γ a b c d e t _
        = pcdE19RhsInner K Γ a b c d e t _
      rw [pcdE19LhsInner_apply, pcdE19RhsInner_apply]
      exact recog_E19M_pcd_generator K Γ a b c d e ht hr hs p

/-- Edge 19 becomes the closed fifth pentagon edge at `(a,b,c+d,e)`
after extracting `F_{c,d}`. -/
theorem recog_E19M_pcd :
    (omegaPcdV13 K Γ a b c d e).toLinearMap ∘ₗ E19M K Γ a b c d e
      = smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
          (pcdE19Map K Γ a b c d e) (gParity K Γ a b (c + d + e))
          (pcdE19Map_hg K Γ a b c d e)
          ∘ₗ (omegaPcdV8 K Γ a b c d e).toLinearMap := by
  apply LinearMap.ext
  intro z
  induction z using pcdV8_induction_on_left_homog K Γ a b c d e with
  | zero => simp only [map_zero]
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | homog j t n ht =>
      exact LinearMap.congr_fun (pcdE19Inner_maps_eq K Γ a b c d e ht) n


end GaugeChi

end Superfusion
