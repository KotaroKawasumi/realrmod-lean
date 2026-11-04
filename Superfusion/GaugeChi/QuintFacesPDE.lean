/-
Superfusion / GaugeChi / QuintFacesPDE

Closure of the `(d+e)`-cluster pentagon face.  The five edge
recognitions in `QuintExtract2`--`QuintExtractPDE` identify the original
quintuple edges with signed amplifications of the five canonical
pentagon edges after extracting the common spectator `F_{d,e}`.  The
proof below only composes those recognitions, applies
`gParity_cocycle` and `gChiCanon_spec`, and cancels the extraction
equivalence.
-/
import Superfusion.GaugeChi.QuintExtractPDE

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

/-! ### The five shifted pentagon maps and their total degrees -/

private noncomputable def pdeGE1 :
    GQ1 K Γ a b c (d + e) →ₗ[K] GQ2 K Γ a b c (d + e) :=
  GE1 K Γ a b c (d + e) (gTCanon K Γ a b c).toLinearMap
    (gCanonRight K Γ a b c)

private noncomputable def pdeGE2 :
    GQ2 K Γ a b c (d + e) →ₗ[K] GQ3 K Γ a b c (d + e) :=
  GE2 K Γ a b c (d + e) (gParity K Γ a (b + c) (d + e))
    (gt2Canon K Γ a b c (d + e)
      (gTCanon K Γ a (b + c) (d + e))).toLinearMap
    (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) (d + e))
      (gParity K Γ a (b + c) (d + e))
      (gTCanon_mem_gInterSpace K Γ a (b + c) (d + e)))

private noncomputable def pdeGE3 :
    GQ3 K Γ a b c (d + e) →ₗ[K] GQ4 K Γ a b c (d + e) :=
  GE3 K Γ a b c (d + e) (gTCanon K Γ b c (d + e)).toLinearMap
    (gCanonRight K Γ b c (d + e))

private noncomputable def pdeGE4 :
    GQ1 K Γ a b c (d + e) →ₗ[K] GQ5 K Γ a b c (d + e) :=
  GE4 K Γ a b c (d + e) (gParity K Γ (a + b) c (d + e))
    (gTCanon K Γ (a + b) c (d + e)).toLinearMap
    (gCanonHphi4 K Γ a b c (d + e))

private noncomputable def pdeTopRoute :
    GQ1 K Γ a b c (d + e) →ₗ[K] GQ4 K Γ a b c (d + e) :=
  pdeGE3 K Γ a b c d e ∘ₗ
    pdeGE2 K Γ a b c d e ∘ₗ pdeGE1 K Γ a b c d e

private noncomputable def pdeBotRoute :
    GQ1 K Γ a b c (d + e) →ₗ[K] GQ4 K Γ a b c (d + e) :=
  pdeE21Map K Γ a b c d e ∘ₗ pdeGE4 K Γ a b c d e

private noncomputable def pdeTopDegree : ZMod 2 :=
  gParity K Γ b c (d + e) +
    (gParity K Γ a (b + c) (d + e) + gParity K Γ a b c)

private noncomputable def pdeBotDegree : ZMod 2 :=
  gParity K Γ a b (c + (d + e)) +
    gParity K Γ (a + b) c (d + e)

/-! ### Signed equivariance of the two route composites -/

private theorem pdeTopRoute_hg :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (d + e)).carrier⦄,
      τ ∈ (Γ.D (d + e)).grading i →
      ∀ n : GQ1 K Γ a b c (d + e),
        pdeTopRoute K Γ a b c d e (τ • n)
          = ((sgn (pdeTopDegree K Γ a b c d e * i) : ℤˣ) : ℤ) •
              (τ • pdeTopRoute K Γ a b c d e n) := by
  unfold pdeTopRoute pdeTopDegree
  exact signedEquivariant_comp (Γ.D (d + e)).grading
    ((pdeGE2 K Γ a b c d e).comp (pdeGE1 K Γ a b c d e))
    (gParity K Γ a (b + c) (d + e) + gParity K Γ a b c)
    (pdeGE3 K Γ a b c d e) (gParity K Γ b c (d + e))
    (signedEquivariant_comp (Γ.D (d + e)).grading
      (pdeGE1 K Γ a b c d e) (gParity K Γ a b c)
      (pdeGE2 K Γ a b c d e) (gParity K Γ a (b + c) (d + e))
      (hg1 K Γ a b c d e) (hg2 K Γ a b c d e))
    (hg3 K Γ a b c d e)

private theorem pdeBotRoute_hg :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (d + e)).carrier⦄,
      τ ∈ (Γ.D (d + e)).grading i →
      ∀ n : GQ1 K Γ a b c (d + e),
        pdeBotRoute K Γ a b c d e (τ • n)
          = ((sgn (pdeBotDegree K Γ a b c d e * i) : ℤˣ) : ℤ) •
              (τ • pdeBotRoute K Γ a b c d e n) := by
  unfold pdeBotRoute pdeBotDegree
  exact signedEquivariant_comp (Γ.D (d + e)).grading
    (pdeGE4 K Γ a b c d e) (gParity K Γ (a + b) c (d + e))
    (pdeE21Map K Γ a b c d e) (gParity K Γ a b (c + (d + e)))
    (hg4 K Γ a b c d e) (pdeE21Map_hg K Γ a b c d e)

/-! ### Composition of the signed amplifications -/

private theorem pdeTop_smap :
    smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
          (pdeGE3 K Γ a b c d e) (gParity K Γ b c (d + e))
          (hg3 K Γ a b c d e)
      ∘ₗ smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
          (pdeGE2 K Γ a b c d e) (gParity K Γ a (b + c) (d + e))
          (hg2 K Γ a b c d e)
      ∘ₗ smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
          (pdeGE1 K Γ a b c d e) (gParity K Γ a b c)
          (hg1 K Γ a b c d e)
      = smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
          (pdeTopRoute K Γ a b c d e) (pdeTopDegree K Γ a b c d e)
          (pdeTopRoute_hg K Γ a b c d e) := by
  calc
    _ = smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
          (pdeGE3 K Γ a b c d e) (gParity K Γ b c (d + e))
          (hg3 K Γ a b c d e)
        ∘ₗ smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
          ((pdeGE2 K Γ a b c d e).comp (pdeGE1 K Γ a b c d e))
          (gParity K Γ a (b + c) (d + e) + gParity K Γ a b c)
          (signedEquivariant_comp (Γ.D (d + e)).grading
            (pdeGE1 K Γ a b c d e) (gParity K Γ a b c)
            (pdeGE2 K Γ a b c d e) (gParity K Γ a (b + c) (d + e))
            (hg1 K Γ a b c d e) (hg2 K Γ a b c d e)) := by
      rw [smap_comp_smap (Γ.D (d + e)).grading
        (FusionColumn.grading (Γ.fuse d e))
        (pdeGE1 K Γ a b c d e) (gParity K Γ a b c)
        (pdeGE2 K Γ a b c d e) (gParity K Γ a (b + c) (d + e))
        (hg1 K Γ a b c d e) (hg2 K Γ a b c d e)]
    _ = smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
          ((pdeGE3 K Γ a b c d e).comp
            ((pdeGE2 K Γ a b c d e).comp (pdeGE1 K Γ a b c d e)))
          (gParity K Γ b c (d + e) +
            (gParity K Γ a (b + c) (d + e) + gParity K Γ a b c))
          (signedEquivariant_comp (Γ.D (d + e)).grading
            ((pdeGE2 K Γ a b c d e).comp (pdeGE1 K Γ a b c d e))
            (gParity K Γ a (b + c) (d + e) + gParity K Γ a b c)
            (pdeGE3 K Γ a b c d e) (gParity K Γ b c (d + e))
            (signedEquivariant_comp (Γ.D (d + e)).grading
              (pdeGE1 K Γ a b c d e) (gParity K Γ a b c)
              (pdeGE2 K Γ a b c d e) (gParity K Γ a (b + c) (d + e))
              (hg1 K Γ a b c d e) (hg2 K Γ a b c d e))
            (hg3 K Γ a b c d e)) :=
      smap_comp_smap (Γ.D (d + e)).grading
        (FusionColumn.grading (Γ.fuse d e))
        ((pdeGE2 K Γ a b c d e).comp (pdeGE1 K Γ a b c d e))
        (gParity K Γ a (b + c) (d + e) + gParity K Γ a b c)
        (pdeGE3 K Γ a b c d e) (gParity K Γ b c (d + e))
        (signedEquivariant_comp (Γ.D (d + e)).grading
          (pdeGE1 K Γ a b c d e) (gParity K Γ a b c)
          (pdeGE2 K Γ a b c d e) (gParity K Γ a (b + c) (d + e))
          (hg1 K Γ a b c d e) (hg2 K Γ a b c d e))
        (hg3 K Γ a b c d e)
    _ = _ := rfl

private theorem pdeBot_smap :
    smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
          (pdeE21Map K Γ a b c d e) (gParity K Γ a b (c + (d + e)))
          (pdeE21Map_hg K Γ a b c d e)
      ∘ₗ smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
          (pdeGE4 K Γ a b c d e) (gParity K Γ (a + b) c (d + e))
          (hg4 K Γ a b c d e)
      = smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
          (pdeBotRoute K Γ a b c d e) (pdeBotDegree K Γ a b c d e)
          (pdeBotRoute_hg K Γ a b c d e) := by
  exact (smap_comp_smap (Γ.D (d + e)).grading
    (FusionColumn.grading (Γ.fuse d e))
    (pdeGE4 K Γ a b c d e) (gParity K Γ (a + b) c (d + e))
    (pdeE21Map K Γ a b c d e) (gParity K Γ a b (c + (d + e)))
    (hg4 K Γ a b c d e) (pdeE21Map_hg K Γ a b c d e))

/-! ### The two extracted edge routes -/

private theorem facePDE_top :
    (omegaV14 K Γ a b c d e).toLinearMap ∘ₗ
        E10M K Γ a b c d e ∘ₗ E17M K Γ a b c d e ∘ₗ E20M K Γ a b c d e
      = smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
          (pdeTopRoute K Γ a b c d e) (pdeTopDegree K Γ a b c d e)
          (pdeTopRoute_hg K Γ a b c d e)
          ∘ₗ (omegaV6 K Γ a b c d e).toLinearMap := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  have h10 := LinearMap.congr_fun (recog_E10M K Γ a b c d e)
    (E17M K Γ a b c d e (E20M K Γ a b c d e x))
  have h17 := LinearMap.congr_fun (recog_E17M K Γ a b c d e)
    (E20M K Γ a b c d e x)
  have h20 := LinearMap.congr_fun (recog_E20M K Γ a b c d e) x
  simp only [LinearMap.comp_apply] at h10 h17 h20
  rw [h10, h17, h20]
  exact LinearMap.congr_fun (pdeTop_smap K Γ a b c d e)
    ((omegaV6 K Γ a b c d e).toLinearMap x)

private theorem facePDE_bot :
    (omegaV14 K Γ a b c d e).toLinearMap ∘ₗ
        E21M K Γ a b c d e ∘ₗ E14M K Γ a b c d e
      = smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
          (pdeBotRoute K Γ a b c d e) (pdeBotDegree K Γ a b c d e)
          (pdeBotRoute_hg K Γ a b c d e)
          ∘ₗ (omegaV6 K Γ a b c d e).toLinearMap := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  have h21 := LinearMap.congr_fun (recog_E21M K Γ a b c d e)
    (E14M K Γ a b c d e x)
  have h14 := LinearMap.congr_fun (recog_E14M K Γ a b c d e) x
  simp only [LinearMap.comp_apply] at h21 h14
  rw [h21, h14]
  exact LinearMap.congr_fun (pdeBot_smap K Γ a b c d e)
    ((omegaV6 K Γ a b c d e).toLinearMap x)

/-! ### Transport of the canonical pentagon equation through `smap` -/

private theorem pdeSmap_congr
    {f₁ f₂ : GQ1 K Γ a b c (d + e) →ₗ[K] GQ4 K Γ a b c (d + e)}
    (hff : f₁ = f₂) {q₁ q₂ : ZMod 2} (hqq : q₁ = q₂)
    {hf₁ : ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (d + e)).carrier⦄,
      τ ∈ (Γ.D (d + e)).grading i → ∀ n : GQ1 K Γ a b c (d + e),
        f₁ (τ • n) = ((sgn (q₁ * i) : ℤˣ) : ℤ) • (τ • f₁ n)}
    {hf₂ : ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (d + e)).carrier⦄,
      τ ∈ (Γ.D (d + e)).grading i → ∀ n : GQ1 K Γ a b c (d + e),
        f₂ (τ • n) = ((sgn (q₂ * i) : ℤˣ) : ℤ) • (τ • f₂ n)} :
    smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
        f₁ q₁ hf₁
      = smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
          f₂ q₂ hf₂ := by
  subst hff
  subst hqq
  rfl

private theorem pde_smap_routes :
    smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
        (pdeTopRoute K Γ a b c d e) (pdeTopDegree K Γ a b c d e)
        (pdeTopRoute_hg K Γ a b c d e)
      = gChiCanon K Γ a b c (d + e) •
          smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
            (pdeBotRoute K Γ a b c d e) (pdeBotDegree K Γ a b c d e)
            (pdeBotRoute_hg K Γ a b c d e) := by
  have hdeg : pdeTopDegree K Γ a b c d e = pdeBotDegree K Γ a b c d e := by
    unfold pdeTopDegree pdeBotDegree
    calc
      gParity K Γ b c (d + e) +
          (gParity K Γ a (b + c) (d + e) + gParity K Γ a b c)
        = gParity K Γ a b c + gParity K Γ a (b + c) (d + e) +
            gParity K Γ b c (d + e) := by ring
      _ = gParity K Γ (a + b) c (d + e) +
            gParity K Γ a b (c + (d + e)) :=
        gParity_cocycle K Γ a b c (d + e)
      _ = gParity K Γ a b (c + (d + e)) +
            gParity K Γ (a + b) c (d + e) := by ring
  have hroute : pdeTopRoute K Γ a b c d e
      = gChiCanon K Γ a b c (d + e) • pdeBotRoute K Γ a b c d e := by
    have hbot : pdeBotRoute K Γ a b c d e
        = gBotRoute K Γ a b c (d + e)
            (gParity K Γ (a + b) c (d + e))
            (gTCanon K Γ (a + b) c (d + e)).toLinearMap
            (gCanonHphi4 K Γ a b c (d + e))
            (gParity K Γ a b (c + (d + e)))
            (gTCanon K Γ a b (c + (d + e))).toLinearMap
            (gCanonHphi5 K Γ a b c (d + e)) := by
      unfold pdeBotRoute pdeE21Map pdeGE4 gBotRoute
      exact LinearMap.comp_assoc _ _ _
    rw [hbot]
    simpa only [pdeTopRoute, pdeGE1, pdeGE2, pdeGE3, gTopRoute] using
      (gChiCanon_spec K Γ a b c (d + e))
  calc
    smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
        (pdeTopRoute K Γ a b c d e) (pdeTopDegree K Γ a b c d e)
        (pdeTopRoute_hg K Γ a b c d e)
      = smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
          (gChiCanon K Γ a b c (d + e) • pdeBotRoute K Γ a b c d e)
          (pdeBotDegree K Γ a b c d e)
          (fun i τ hτ n => by
            rw [LinearMap.smul_apply, pdeBotRoute_hg K Γ a b c d e hτ n,
              LinearMap.smul_apply, smul_comm (gChiCanon K Γ a b c (d + e)),
              smul_comm (gChiCanon K Γ a b c (d + e)) τ]) :=
        pdeSmap_congr K Γ a b c d e hroute hdeg
    _ = gChiCanon K Γ a b c (d + e) •
          smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
            (pdeBotRoute K Γ a b c d e) (pdeBotDegree K Γ a b c d e)
            (pdeBotRoute_hg K Γ a b c d e) :=
      smap_smul K (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
        (pdeBotRoute K Γ a b c d e) (pdeBotDegree K Γ a b c d e)
        (pdeBotRoute_hg K Γ a b c d e) (gChiCanon K Γ a b c (d + e))

/-! ### The `(d+e)`-cluster pentagon face -/

/-- **`face_PDE`**: the pentagon at `(a,b,c,d+e)`, signed-whiskered by
the extracted spectator `F_{d,e}`, in the orientation of
`gChiCanon_spec`. -/
theorem face_PDE :
    E10M K Γ a b c d e ∘ₗ E17M K Γ a b c d e ∘ₗ E20M K Γ a b c d e
      = gChiCanon K Γ a b c (d + e) •
          (E21M K Γ a b c d e ∘ₗ E14M K Γ a b c d e) := by
  apply LinearMap.ext
  intro x
  apply (omegaV14 K Γ a b c d e).injective
  calc
    (omegaV14 K Γ a b c d e)
        ((E10M K Γ a b c d e ∘ₗ E17M K Γ a b c d e ∘ₗ
          E20M K Γ a b c d e) x)
      = smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
          (pdeTopRoute K Γ a b c d e) (pdeTopDegree K Γ a b c d e)
          (pdeTopRoute_hg K Γ a b c d e)
          ((omegaV6 K Γ a b c d e) x) :=
        LinearMap.congr_fun (facePDE_top K Γ a b c d e) x
    _ = gChiCanon K Γ a b c (d + e) •
          smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
            (pdeBotRoute K Γ a b c d e) (pdeBotDegree K Γ a b c d e)
            (pdeBotRoute_hg K Γ a b c d e)
            ((omegaV6 K Γ a b c d e) x) :=
        LinearMap.congr_fun (pde_smap_routes K Γ a b c d e)
          ((omegaV6 K Γ a b c d e) x)
    _ = gChiCanon K Γ a b c (d + e) •
          (omegaV14 K Γ a b c d e)
            ((E21M K Γ a b c d e ∘ₗ E14M K Γ a b c d e) x) := by
        have hbot := LinearMap.congr_fun (facePDE_bot K Γ a b c d e) x
        simp only [LinearMap.comp_apply] at hbot
        simp only [LinearMap.comp_apply]
        exact congrArg (fun z => gChiCanon K Γ a b c (d + e) • z) hbot.symm
    _ = (omegaV14 K Γ a b c d e)
          ((gChiCanon K Γ a b c (d + e) •
            (E21M K Γ a b c d e ∘ₗ E14M K Γ a b c d e)) x) := by
        rw [LinearMap.smul_apply, map_smul]

end GaugeChi

end Superfusion
