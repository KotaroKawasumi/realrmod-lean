/-
Superfusion / GaugeChi / QuintFacesPCD

Closure of the `(c+d)`-cluster pentagon face.  The five recognitions in
`QuintRecogPCD` identify the original quintuple edges with signed
amplifications of the five canonical pentagon edges at `(a,b,c+d,e)`
after extracting the common spectator `F_{c,d}`.
-/
import Superfusion.GaugeChi.QuintRecogPCD

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

/-! ### The two shifted pentagon routes and their total degrees -/

private noncomputable def pcdTopRoute :
    GQ1 K Γ a b (c + d) e →ₗ[K] GQ4 K Γ a b (c + d) e :=
  pcdGE3 K Γ a b c d e ∘ₗ
    pcdGE2 K Γ a b c d e ∘ₗ pcdGE1 K Γ a b c d e

private noncomputable def pcdBotRoute :
    GQ1 K Γ a b (c + d) e →ₗ[K] GQ4 K Γ a b (c + d) e :=
  pcdE19Map K Γ a b c d e ∘ₗ pcdGE4 K Γ a b c d e

private noncomputable def pcdTopDegree : ZMod 2 :=
  gParity K Γ b (c + d) e +
    (gParity K Γ a (b + (c + d)) e + gParity K Γ a b (c + d))

private noncomputable def pcdBotDegree : ZMod 2 :=
  gParity K Γ a b (c + d + e) +
    gParity K Γ (a + b) (c + d) e

/-! ### Signed equivariance of the route composites -/

private theorem pcdTopRoute_hg :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (c + d)).carrier⦄,
      τ ∈ (Γ.D (c + d)).grading i →
      ∀ n : GQ1 K Γ a b (c + d) e,
        pcdTopRoute K Γ a b c d e (τ • n)
          = ((sgn (pcdTopDegree K Γ a b c d e * i) : ℤˣ) : ℤ) •
              (τ • pcdTopRoute K Γ a b c d e n) := by
  unfold pcdTopRoute pcdTopDegree
  exact signedEquivariant_comp (Γ.D (c + d)).grading
    ((pcdGE2 K Γ a b c d e).comp (pcdGE1 K Γ a b c d e))
    (gParity K Γ a (b + (c + d)) e + gParity K Γ a b (c + d))
    (pcdGE3 K Γ a b c d e) (gParity K Γ b (c + d) e)
    (signedEquivariant_comp (Γ.D (c + d)).grading
      (pcdGE1 K Γ a b c d e) (gParity K Γ a b (c + d))
      (pcdGE2 K Γ a b c d e) (gParity K Γ a (b + (c + d)) e)
      (pcdHg1 K Γ a b c d e) (pcdHg2 K Γ a b c d e))
    (pcdHg3 K Γ a b c d e)

private theorem pcdBotRoute_hg :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (c + d)).carrier⦄,
      τ ∈ (Γ.D (c + d)).grading i →
      ∀ n : GQ1 K Γ a b (c + d) e,
        pcdBotRoute K Γ a b c d e (τ • n)
          = ((sgn (pcdBotDegree K Γ a b c d e * i) : ℤˣ) : ℤ) •
              (τ • pcdBotRoute K Γ a b c d e n) := by
  unfold pcdBotRoute pcdBotDegree
  exact signedEquivariant_comp (Γ.D (c + d)).grading
    (pcdGE4 K Γ a b c d e) (gParity K Γ (a + b) (c + d) e)
    (pcdE19Map K Γ a b c d e) (gParity K Γ a b (c + d + e))
    (pcdHg4 K Γ a b c d e) (pcdE19Map_hg K Γ a b c d e)

/-! ### Composition of the signed amplifications -/

private theorem pcdTop_smap :
    smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
          (pcdGE3 K Γ a b c d e) (gParity K Γ b (c + d) e)
          (pcdHg3 K Γ a b c d e)
      ∘ₗ smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
          (pcdGE2 K Γ a b c d e) (gParity K Γ a (b + (c + d)) e)
          (pcdHg2 K Γ a b c d e)
      ∘ₗ smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
          (pcdGE1 K Γ a b c d e) (gParity K Γ a b (c + d))
          (pcdHg1 K Γ a b c d e)
      = smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
          (pcdTopRoute K Γ a b c d e) (pcdTopDegree K Γ a b c d e)
          (pcdTopRoute_hg K Γ a b c d e) := by
  calc
    _ = smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
          (pcdGE3 K Γ a b c d e) (gParity K Γ b (c + d) e)
          (pcdHg3 K Γ a b c d e)
        ∘ₗ smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
          ((pcdGE2 K Γ a b c d e).comp (pcdGE1 K Γ a b c d e))
          (gParity K Γ a (b + (c + d)) e + gParity K Γ a b (c + d))
          (signedEquivariant_comp (Γ.D (c + d)).grading
            (pcdGE1 K Γ a b c d e) (gParity K Γ a b (c + d))
            (pcdGE2 K Γ a b c d e) (gParity K Γ a (b + (c + d)) e)
            (pcdHg1 K Γ a b c d e) (pcdHg2 K Γ a b c d e)) := by
      rw [smap_comp_smap (Γ.D (c + d)).grading
        (FusionColumn.grading (Γ.fuse c d))
        (pcdGE1 K Γ a b c d e) (gParity K Γ a b (c + d))
        (pcdGE2 K Γ a b c d e) (gParity K Γ a (b + (c + d)) e)
        (pcdHg1 K Γ a b c d e) (pcdHg2 K Γ a b c d e)]
    _ = smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
          ((pcdGE3 K Γ a b c d e).comp
            ((pcdGE2 K Γ a b c d e).comp (pcdGE1 K Γ a b c d e)))
          (gParity K Γ b (c + d) e +
            (gParity K Γ a (b + (c + d)) e + gParity K Γ a b (c + d)))
          (signedEquivariant_comp (Γ.D (c + d)).grading
            ((pcdGE2 K Γ a b c d e).comp (pcdGE1 K Γ a b c d e))
            (gParity K Γ a (b + (c + d)) e + gParity K Γ a b (c + d))
            (pcdGE3 K Γ a b c d e) (gParity K Γ b (c + d) e)
            (signedEquivariant_comp (Γ.D (c + d)).grading
              (pcdGE1 K Γ a b c d e) (gParity K Γ a b (c + d))
              (pcdGE2 K Γ a b c d e) (gParity K Γ a (b + (c + d)) e)
              (pcdHg1 K Γ a b c d e) (pcdHg2 K Γ a b c d e))
            (pcdHg3 K Γ a b c d e)) :=
      smap_comp_smap (Γ.D (c + d)).grading
        (FusionColumn.grading (Γ.fuse c d))
        ((pcdGE2 K Γ a b c d e).comp (pcdGE1 K Γ a b c d e))
        (gParity K Γ a (b + (c + d)) e + gParity K Γ a b (c + d))
        (pcdGE3 K Γ a b c d e) (gParity K Γ b (c + d) e)
        (signedEquivariant_comp (Γ.D (c + d)).grading
          (pcdGE1 K Γ a b c d e) (gParity K Γ a b (c + d))
          (pcdGE2 K Γ a b c d e) (gParity K Γ a (b + (c + d)) e)
          (pcdHg1 K Γ a b c d e) (pcdHg2 K Γ a b c d e))
        (pcdHg3 K Γ a b c d e)
    _ = _ := rfl

private theorem pcdBot_smap :
    smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
          (pcdE19Map K Γ a b c d e) (gParity K Γ a b (c + d + e))
          (pcdE19Map_hg K Γ a b c d e)
      ∘ₗ smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
          (pcdGE4 K Γ a b c d e) (gParity K Γ (a + b) (c + d) e)
          (pcdHg4 K Γ a b c d e)
      = smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
          (pcdBotRoute K Γ a b c d e) (pcdBotDegree K Γ a b c d e)
          (pcdBotRoute_hg K Γ a b c d e) := by
  exact smap_comp_smap (Γ.D (c + d)).grading
    (FusionColumn.grading (Γ.fuse c d))
    (pcdGE4 K Γ a b c d e) (gParity K Γ (a + b) (c + d) e)
    (pcdE19Map K Γ a b c d e) (gParity K Γ a b (c + d + e))
    (pcdHg4 K Γ a b c d e) (pcdE19Map_hg K Γ a b c d e)

/-! ### The two extracted edge routes -/

private theorem facePCD_top :
    (omegaPcdV13 K Γ a b c d e).toLinearMap ∘ₗ
        E7M K Γ a b c d e ∘ₗ E18M K Γ a b c d e ∘ₗ E5M K Γ a b c d e
      = smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
          (pcdTopRoute K Γ a b c d e) (pcdTopDegree K Γ a b c d e)
          (pcdTopRoute_hg K Γ a b c d e)
          ∘ₗ (omegaPcdV3 K Γ a b c d e).toLinearMap := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  have h7 := LinearMap.congr_fun (recog_E7M_pcd K Γ a b c d e)
    (E18M K Γ a b c d e (E5M K Γ a b c d e x))
  have h18 := LinearMap.congr_fun (recog_E18M_pcd K Γ a b c d e)
    (E5M K Γ a b c d e x)
  have h5 := LinearMap.congr_fun (recog_E5M_pcd K Γ a b c d e) x
  simp only [LinearMap.comp_apply] at h7 h18 h5
  rw [h7, h18, h5]
  exact LinearMap.congr_fun (pcdTop_smap K Γ a b c d e)
    ((omegaPcdV3 K Γ a b c d e).toLinearMap x)

private theorem facePCD_bot :
    (omegaPcdV13 K Γ a b c d e).toLinearMap ∘ₗ
        E19M K Γ a b c d e ∘ₗ E11M K Γ a b c d e
      = smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
          (pcdBotRoute K Γ a b c d e) (pcdBotDegree K Γ a b c d e)
          (pcdBotRoute_hg K Γ a b c d e)
          ∘ₗ (omegaPcdV3 K Γ a b c d e).toLinearMap := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  have h19 := LinearMap.congr_fun (recog_E19M_pcd K Γ a b c d e)
    (E11M K Γ a b c d e x)
  have h11 := LinearMap.congr_fun (recog_E11M_pcd K Γ a b c d e) x
  simp only [LinearMap.comp_apply] at h19 h11
  rw [h19, h11]
  exact LinearMap.congr_fun (pcdBot_smap K Γ a b c d e)
    ((omegaPcdV3 K Γ a b c d e).toLinearMap x)

/-! ### Transport of the canonical pentagon equation through `smap` -/

private theorem pcdSmap_congr
    {f₁ f₂ : GQ1 K Γ a b (c + d) e →ₗ[K] GQ4 K Γ a b (c + d) e}
    (hff : f₁ = f₂) {q₁ q₂ : ZMod 2} (hqq : q₁ = q₂)
    {hf₁ : ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (c + d)).carrier⦄,
      τ ∈ (Γ.D (c + d)).grading i → ∀ n : GQ1 K Γ a b (c + d) e,
        f₁ (τ • n) = ((sgn (q₁ * i) : ℤˣ) : ℤ) • (τ • f₁ n)}
    {hf₂ : ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (c + d)).carrier⦄,
      τ ∈ (Γ.D (c + d)).grading i → ∀ n : GQ1 K Γ a b (c + d) e,
        f₂ (τ • n) = ((sgn (q₂ * i) : ℤˣ) : ℤ) • (τ • f₂ n)} :
    smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
        f₁ q₁ hf₁
      = smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
          f₂ q₂ hf₂ := by
  subst hff
  subst hqq
  rfl

private theorem pcd_smap_routes :
    smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
        (pcdTopRoute K Γ a b c d e) (pcdTopDegree K Γ a b c d e)
        (pcdTopRoute_hg K Γ a b c d e)
      = gChiCanon K Γ a b (c + d) e •
          smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
            (pcdBotRoute K Γ a b c d e) (pcdBotDegree K Γ a b c d e)
            (pcdBotRoute_hg K Γ a b c d e) := by
  have hdeg : pcdTopDegree K Γ a b c d e = pcdBotDegree K Γ a b c d e := by
    unfold pcdTopDegree pcdBotDegree
    calc
      gParity K Γ b (c + d) e +
          (gParity K Γ a (b + (c + d)) e + gParity K Γ a b (c + d))
        = gParity K Γ a b (c + d) + gParity K Γ a (b + (c + d)) e +
            gParity K Γ b (c + d) e := by ring
      _ = gParity K Γ (a + b) (c + d) e +
            gParity K Γ a b (c + d + e) :=
        gParity_cocycle K Γ a b (c + d) e
      _ = gParity K Γ a b (c + d + e) +
            gParity K Γ (a + b) (c + d) e := by ring
  have hroute : pcdTopRoute K Γ a b c d e
      = gChiCanon K Γ a b (c + d) e • pcdBotRoute K Γ a b c d e := by
    have hbot : pcdBotRoute K Γ a b c d e
        = gBotRoute K Γ a b (c + d) e
            (gParity K Γ (a + b) (c + d) e)
            (gTCanon K Γ (a + b) (c + d) e).toLinearMap
            (gCanonHphi4 K Γ a b (c + d) e)
            (gParity K Γ a b (c + d + e))
            (gTCanon K Γ a b (c + d + e)).toLinearMap
            (gCanonHphi5 K Γ a b (c + d) e) := by
      unfold pcdBotRoute pcdE19Map pcdGE4 gBotRoute
      exact LinearMap.comp_assoc _ _ _
    rw [hbot]
    simpa only [pcdTopRoute, pcdGE1, pcdGE2, pcdGE3, gTopRoute] using
      (gChiCanon_spec K Γ a b (c + d) e)
  calc
    smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
        (pcdTopRoute K Γ a b c d e) (pcdTopDegree K Γ a b c d e)
        (pcdTopRoute_hg K Γ a b c d e)
      = smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
          (gChiCanon K Γ a b (c + d) e • pcdBotRoute K Γ a b c d e)
          (pcdBotDegree K Γ a b c d e)
          (fun i τ hτ n => by
            rw [LinearMap.smul_apply, pcdBotRoute_hg K Γ a b c d e hτ n,
              LinearMap.smul_apply, smul_comm (gChiCanon K Γ a b (c + d) e),
              smul_comm (gChiCanon K Γ a b (c + d) e) τ]) :=
        pcdSmap_congr K Γ a b c d e hroute hdeg
    _ = gChiCanon K Γ a b (c + d) e •
          smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
            (pcdBotRoute K Γ a b c d e) (pcdBotDegree K Γ a b c d e)
            (pcdBotRoute_hg K Γ a b c d e) :=
      smap_smul K (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
        (pcdBotRoute K Γ a b c d e) (pcdBotDegree K Γ a b c d e)
        (pcdBotRoute_hg K Γ a b c d e) (gChiCanon K Γ a b (c + d) e)

/-! ### The `(c+d)`-cluster pentagon face -/

/-- **`face_PCD`**: the pentagon at `(a,b,c+d,e)`, signed-whiskered by
the extracted spectator `F_{c,d}`, in the orientation of
`gChiCanon_spec`. -/
theorem face_PCD :
    E7M K Γ a b c d e ∘ₗ E18M K Γ a b c d e ∘ₗ E5M K Γ a b c d e
      = gChiCanon K Γ a b (c + d) e •
          (E19M K Γ a b c d e ∘ₗ E11M K Γ a b c d e) := by
  apply LinearMap.ext
  intro x
  apply (omegaPcdV13 K Γ a b c d e).injective
  calc
    (omegaPcdV13 K Γ a b c d e)
        ((E7M K Γ a b c d e ∘ₗ E18M K Γ a b c d e ∘ₗ
          E5M K Γ a b c d e) x)
      = smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
          (pcdTopRoute K Γ a b c d e) (pcdTopDegree K Γ a b c d e)
          (pcdTopRoute_hg K Γ a b c d e)
          ((omegaPcdV3 K Γ a b c d e) x) :=
        LinearMap.congr_fun (facePCD_top K Γ a b c d e) x
    _ = gChiCanon K Γ a b (c + d) e •
          smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
            (pcdBotRoute K Γ a b c d e) (pcdBotDegree K Γ a b c d e)
            (pcdBotRoute_hg K Γ a b c d e)
            ((omegaPcdV3 K Γ a b c d e) x) :=
        LinearMap.congr_fun (pcd_smap_routes K Γ a b c d e)
          ((omegaPcdV3 K Γ a b c d e) x)
    _ = gChiCanon K Γ a b (c + d) e •
          (omegaPcdV13 K Γ a b c d e)
            ((E19M K Γ a b c d e ∘ₗ E11M K Γ a b c d e) x) := by
        have hbot := LinearMap.congr_fun (facePCD_bot K Γ a b c d e) x
        simp only [LinearMap.comp_apply] at hbot
        simp only [LinearMap.comp_apply]
        exact congrArg (fun z => gChiCanon K Γ a b (c + d) e • z) hbot.symm
    _ = (omegaPcdV13 K Γ a b c d e)
          ((gChiCanon K Γ a b (c + d) e •
            (E19M K Γ a b c d e ∘ₗ E11M K Γ a b c d e)) x) := by
        rw [LinearMap.smul_apply, map_smul]

end GaugeChi

end Superfusion
