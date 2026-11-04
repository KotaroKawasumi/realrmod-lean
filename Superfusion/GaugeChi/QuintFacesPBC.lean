/-
Superfusion / GaugeChi / QuintFacesPBC

Closure of the `(b+c)`-cluster pentagon face.  The five recognitions in
`QuintRecogPBC` identify the original quintuple edges with signed
amplifications of the five canonical pentagon edges at `(a,b+c,d,e)`
after extracting the common spectator `F_{b,c}`.  The proof composes
those recognitions, invokes `gParity_cocycle` and `gChiCanon_spec`, and
cancels the extraction equivalence.
-/
import Superfusion.GaugeChi.QuintRecogPBC

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

private noncomputable def pbcGE1 :
    GQ1 K Γ a (b + c) d e →ₗ[K] GQ2 K Γ a (b + c) d e :=
  GE1 K Γ a (b + c) d e (gTCanon K Γ a (b + c) d).toLinearMap
    (gCanonRight K Γ a (b + c) d)

private noncomputable def pbcGE2 :
    GQ2 K Γ a (b + c) d e →ₗ[K] GQ3 K Γ a (b + c) d e :=
  GE2 K Γ a (b + c) d e (gParity K Γ a (b + c + d) e)
    (gt2Canon K Γ a (b + c) d e
      (gTCanon K Γ a (b + c + d) e)).toLinearMap
    (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c + d) e)
      (gParity K Γ a (b + c + d) e)
      (gTCanon_mem_gInterSpace K Γ a (b + c + d) e))

private noncomputable def pbcGE3 :
    GQ3 K Γ a (b + c) d e →ₗ[K] GQ4 K Γ a (b + c) d e :=
  GE3 K Γ a (b + c) d e (gTCanon K Γ (b + c) d e).toLinearMap
    (gCanonRight K Γ (b + c) d e)

private noncomputable def pbcGE4 :
    GQ1 K Γ a (b + c) d e →ₗ[K] GQ5 K Γ a (b + c) d e :=
  GE4 K Γ a (b + c) d e (gParity K Γ (a + (b + c)) d e)
    (gTCanon K Γ (a + (b + c)) d e).toLinearMap
    (gCanonHphi4 K Γ a (b + c) d e)

private noncomputable def pbcTopRoute :
    GQ1 K Γ a (b + c) d e →ₗ[K] GQ4 K Γ a (b + c) d e :=
  pbcGE3 K Γ a b c d e ∘ₗ
    pbcGE2 K Γ a b c d e ∘ₗ pbcGE1 K Γ a b c d e

private noncomputable def pbcBotRoute :
    GQ1 K Γ a (b + c) d e →ₗ[K] GQ4 K Γ a (b + c) d e :=
  pbcE17Map K Γ a b c d e ∘ₗ pbcGE4 K Γ a b c d e

private noncomputable def pbcTopDegree : ZMod 2 :=
  gParity K Γ (b + c) d e +
    (gParity K Γ a (b + c + d) e + gParity K Γ a (b + c) d)

private noncomputable def pbcBotDegree : ZMod 2 :=
  gParity K Γ a (b + c) (d + e) +
    gParity K Γ (a + (b + c)) d e

/-! ### Signed equivariance of the two route composites -/

private theorem pbcTopRoute_hg :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (b + c)).carrier⦄,
      τ ∈ (Γ.D (b + c)).grading i →
      ∀ n : GQ1 K Γ a (b + c) d e,
        pbcTopRoute K Γ a b c d e (τ • n)
          = ((sgn (pbcTopDegree K Γ a b c d e * i) : ℤˣ) : ℤ) •
              (τ • pbcTopRoute K Γ a b c d e n) := by
  unfold pbcTopRoute pbcTopDegree
  exact signedEquivariant_comp (Γ.D (b + c)).grading
    ((pbcGE2 K Γ a b c d e).comp (pbcGE1 K Γ a b c d e))
    (gParity K Γ a (b + c + d) e + gParity K Γ a (b + c) d)
    (pbcGE3 K Γ a b c d e) (gParity K Γ (b + c) d e)
    (signedEquivariant_comp (Γ.D (b + c)).grading
      (pbcGE1 K Γ a b c d e) (gParity K Γ a (b + c) d)
      (pbcGE2 K Γ a b c d e) (gParity K Γ a (b + c + d) e)
      (pbcHg1 K Γ a b c d e) (pbcHg2 K Γ a b c d e))
    (pbcHg3 K Γ a b c d e)

private theorem pbcBotRoute_hg :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (b + c)).carrier⦄,
      τ ∈ (Γ.D (b + c)).grading i →
      ∀ n : GQ1 K Γ a (b + c) d e,
        pbcBotRoute K Γ a b c d e (τ • n)
          = ((sgn (pbcBotDegree K Γ a b c d e * i) : ℤˣ) : ℤ) •
              (τ • pbcBotRoute K Γ a b c d e n) := by
  unfold pbcBotRoute pbcBotDegree
  exact signedEquivariant_comp (Γ.D (b + c)).grading
    (pbcGE4 K Γ a b c d e) (gParity K Γ (a + (b + c)) d e)
    (pbcE17Map K Γ a b c d e) (gParity K Γ a (b + c) (d + e))
    (pbcHg4 K Γ a b c d e) (pbcE17Map_hg K Γ a b c d e)

/-! ### Composition of the signed amplifications -/

private theorem pbcTop_smap :
    smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
          (pbcGE3 K Γ a b c d e) (gParity K Γ (b + c) d e)
          (pbcHg3 K Γ a b c d e)
      ∘ₗ smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
          (pbcGE2 K Γ a b c d e) (gParity K Γ a (b + c + d) e)
          (pbcHg2 K Γ a b c d e)
      ∘ₗ smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
          (pbcGE1 K Γ a b c d e) (gParity K Γ a (b + c) d)
          (pbcHg1 K Γ a b c d e)
      = smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
          (pbcTopRoute K Γ a b c d e) (pbcTopDegree K Γ a b c d e)
          (pbcTopRoute_hg K Γ a b c d e) := by
  calc
    _ = smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
          (pbcGE3 K Γ a b c d e) (gParity K Γ (b + c) d e)
          (pbcHg3 K Γ a b c d e)
        ∘ₗ smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
          ((pbcGE2 K Γ a b c d e).comp (pbcGE1 K Γ a b c d e))
          (gParity K Γ a (b + c + d) e + gParity K Γ a (b + c) d)
          (signedEquivariant_comp (Γ.D (b + c)).grading
            (pbcGE1 K Γ a b c d e) (gParity K Γ a (b + c) d)
            (pbcGE2 K Γ a b c d e) (gParity K Γ a (b + c + d) e)
            (pbcHg1 K Γ a b c d e) (pbcHg2 K Γ a b c d e)) := by
      rw [smap_comp_smap (Γ.D (b + c)).grading
        (FusionColumn.grading (Γ.fuse b c))
        (pbcGE1 K Γ a b c d e) (gParity K Γ a (b + c) d)
        (pbcGE2 K Γ a b c d e) (gParity K Γ a (b + c + d) e)
        (pbcHg1 K Γ a b c d e) (pbcHg2 K Γ a b c d e)]
    _ = smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
          ((pbcGE3 K Γ a b c d e).comp
            ((pbcGE2 K Γ a b c d e).comp (pbcGE1 K Γ a b c d e)))
          (gParity K Γ (b + c) d e +
            (gParity K Γ a (b + c + d) e + gParity K Γ a (b + c) d))
          (signedEquivariant_comp (Γ.D (b + c)).grading
            ((pbcGE2 K Γ a b c d e).comp (pbcGE1 K Γ a b c d e))
            (gParity K Γ a (b + c + d) e + gParity K Γ a (b + c) d)
            (pbcGE3 K Γ a b c d e) (gParity K Γ (b + c) d e)
            (signedEquivariant_comp (Γ.D (b + c)).grading
              (pbcGE1 K Γ a b c d e) (gParity K Γ a (b + c) d)
              (pbcGE2 K Γ a b c d e) (gParity K Γ a (b + c + d) e)
              (pbcHg1 K Γ a b c d e) (pbcHg2 K Γ a b c d e))
            (pbcHg3 K Γ a b c d e)) :=
      smap_comp_smap (Γ.D (b + c)).grading
        (FusionColumn.grading (Γ.fuse b c))
        ((pbcGE2 K Γ a b c d e).comp (pbcGE1 K Γ a b c d e))
        (gParity K Γ a (b + c + d) e + gParity K Γ a (b + c) d)
        (pbcGE3 K Γ a b c d e) (gParity K Γ (b + c) d e)
        (signedEquivariant_comp (Γ.D (b + c)).grading
          (pbcGE1 K Γ a b c d e) (gParity K Γ a (b + c) d)
          (pbcGE2 K Γ a b c d e) (gParity K Γ a (b + c + d) e)
          (pbcHg1 K Γ a b c d e) (pbcHg2 K Γ a b c d e))
        (pbcHg3 K Γ a b c d e)
    _ = _ := rfl

private theorem pbcBot_smap :
    smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
          (pbcE17Map K Γ a b c d e) (gParity K Γ a (b + c) (d + e))
          (pbcE17Map_hg K Γ a b c d e)
      ∘ₗ smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
          (pbcGE4 K Γ a b c d e) (gParity K Γ (a + (b + c)) d e)
          (pbcHg4 K Γ a b c d e)
      = smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
          (pbcBotRoute K Γ a b c d e) (pbcBotDegree K Γ a b c d e)
          (pbcBotRoute_hg K Γ a b c d e) := by
  exact smap_comp_smap (Γ.D (b + c)).grading
    (FusionColumn.grading (Γ.fuse b c))
    (pbcGE4 K Γ a b c d e) (gParity K Γ (a + (b + c)) d e)
    (pbcE17Map K Γ a b c d e) (gParity K Γ a (b + c) (d + e))
    (pbcHg4 K Γ a b c d e) (pbcE17Map_hg K Γ a b c d e)

/-! ### The two extracted edge routes -/

private theorem facePBC_top :
    (omegaPbcV12 K Γ a b c d e).toLinearMap ∘ₗ
        E9M K Γ a b c d e ∘ₗ E15M K Γ a b c d e ∘ₗ E2M K Γ a b c d e
      = smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
          (pbcTopRoute K Γ a b c d e) (pbcTopDegree K Γ a b c d e)
          (pbcTopRoute_hg K Γ a b c d e)
          ∘ₗ (omegaPbcV2 K Γ a b c d e).toLinearMap := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  have h9 := LinearMap.congr_fun (recog_E9M_pbc K Γ a b c d e)
    (E15M K Γ a b c d e (E2M K Γ a b c d e x))
  have h15 := LinearMap.congr_fun (recog_E15M_pbc K Γ a b c d e)
    (E2M K Γ a b c d e x)
  have h2 := LinearMap.congr_fun (recog_E2M_pbc K Γ a b c d e) x
  simp only [LinearMap.comp_apply] at h9 h15 h2
  rw [h9, h15, h2]
  exact LinearMap.congr_fun (pbcTop_smap K Γ a b c d e)
    ((omegaPbcV2 K Γ a b c d e).toLinearMap x)

private theorem facePBC_bot :
    (omegaPbcV12 K Γ a b c d e).toLinearMap ∘ₗ
        E17M K Γ a b c d e ∘ₗ E16M K Γ a b c d e
      = smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
          (pbcBotRoute K Γ a b c d e) (pbcBotDegree K Γ a b c d e)
          (pbcBotRoute_hg K Γ a b c d e)
          ∘ₗ (omegaPbcV2 K Γ a b c d e).toLinearMap := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  have h17 := LinearMap.congr_fun (recog_E17M_pbc K Γ a b c d e)
    (E16M K Γ a b c d e x)
  have h16 := LinearMap.congr_fun (recog_E16M_pbc K Γ a b c d e) x
  simp only [LinearMap.comp_apply] at h17 h16
  rw [h17, h16]
  exact LinearMap.congr_fun (pbcBot_smap K Γ a b c d e)
    ((omegaPbcV2 K Γ a b c d e).toLinearMap x)

/-! ### Transport of the canonical pentagon equation through `smap` -/

private theorem pbcSmap_congr
    {f₁ f₂ : GQ1 K Γ a (b + c) d e →ₗ[K] GQ4 K Γ a (b + c) d e}
    (hff : f₁ = f₂) {q₁ q₂ : ZMod 2} (hqq : q₁ = q₂)
    {hf₁ : ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (b + c)).carrier⦄,
      τ ∈ (Γ.D (b + c)).grading i → ∀ n : GQ1 K Γ a (b + c) d e,
        f₁ (τ • n) = ((sgn (q₁ * i) : ℤˣ) : ℤ) • (τ • f₁ n)}
    {hf₂ : ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (b + c)).carrier⦄,
      τ ∈ (Γ.D (b + c)).grading i → ∀ n : GQ1 K Γ a (b + c) d e,
        f₂ (τ • n) = ((sgn (q₂ * i) : ℤˣ) : ℤ) • (τ • f₂ n)} :
    smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
        f₁ q₁ hf₁
      = smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
          f₂ q₂ hf₂ := by
  subst hff
  subst hqq
  rfl

private theorem pbc_smap_routes :
    smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
        (pbcTopRoute K Γ a b c d e) (pbcTopDegree K Γ a b c d e)
        (pbcTopRoute_hg K Γ a b c d e)
      = gChiCanon K Γ a (b + c) d e •
          smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
            (pbcBotRoute K Γ a b c d e) (pbcBotDegree K Γ a b c d e)
            (pbcBotRoute_hg K Γ a b c d e) := by
  have hdeg : pbcTopDegree K Γ a b c d e = pbcBotDegree K Γ a b c d e := by
    unfold pbcTopDegree pbcBotDegree
    calc
      gParity K Γ (b + c) d e +
          (gParity K Γ a (b + c + d) e + gParity K Γ a (b + c) d)
        = gParity K Γ a (b + c) d + gParity K Γ a (b + c + d) e +
            gParity K Γ (b + c) d e := by ring
      _ = gParity K Γ (a + (b + c)) d e +
            gParity K Γ a (b + c) (d + e) :=
        gParity_cocycle K Γ a (b + c) d e
      _ = gParity K Γ a (b + c) (d + e) +
            gParity K Γ (a + (b + c)) d e := by ring
  have hroute : pbcTopRoute K Γ a b c d e
      = gChiCanon K Γ a (b + c) d e • pbcBotRoute K Γ a b c d e := by
    have hbot : pbcBotRoute K Γ a b c d e
        = gBotRoute K Γ a (b + c) d e
            (gParity K Γ (a + (b + c)) d e)
            (gTCanon K Γ (a + (b + c)) d e).toLinearMap
            (gCanonHphi4 K Γ a (b + c) d e)
            (gParity K Γ a (b + c) (d + e))
            (gTCanon K Γ a (b + c) (d + e)).toLinearMap
            (gCanonHphi5 K Γ a (b + c) d e) := by
      unfold pbcBotRoute pbcE17Map pbcGE4 gBotRoute
      exact LinearMap.comp_assoc _ _ _
    rw [hbot]
    simpa only [pbcTopRoute, pbcGE1, pbcGE2, pbcGE3, gTopRoute] using
      (gChiCanon_spec K Γ a (b + c) d e)
  calc
    smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
        (pbcTopRoute K Γ a b c d e) (pbcTopDegree K Γ a b c d e)
        (pbcTopRoute_hg K Γ a b c d e)
      = smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
          (gChiCanon K Γ a (b + c) d e • pbcBotRoute K Γ a b c d e)
          (pbcBotDegree K Γ a b c d e)
          (fun i τ hτ n => by
            rw [LinearMap.smul_apply, pbcBotRoute_hg K Γ a b c d e hτ n,
              LinearMap.smul_apply, smul_comm (gChiCanon K Γ a (b + c) d e),
              smul_comm (gChiCanon K Γ a (b + c) d e) τ]) :=
        pbcSmap_congr K Γ a b c d e hroute hdeg
    _ = gChiCanon K Γ a (b + c) d e •
          smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
            (pbcBotRoute K Γ a b c d e) (pbcBotDegree K Γ a b c d e)
            (pbcBotRoute_hg K Γ a b c d e) :=
      smap_smul K (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
        (pbcBotRoute K Γ a b c d e) (pbcBotDegree K Γ a b c d e)
        (pbcBotRoute_hg K Γ a b c d e) (gChiCanon K Γ a (b + c) d e)

/-! ### The `(b+c)`-cluster pentagon face -/

/-- **`face_PBC`**: the pentagon at `(a,b+c,d,e)`, signed-whiskered by
the extracted spectator `F_{b,c}`, in the orientation of
`gChiCanon_spec`. -/
theorem face_PBC :
    E9M K Γ a b c d e ∘ₗ E15M K Γ a b c d e ∘ₗ E2M K Γ a b c d e
      = gChiCanon K Γ a (b + c) d e •
          (E17M K Γ a b c d e ∘ₗ E16M K Γ a b c d e) := by
  apply LinearMap.ext
  intro x
  apply (omegaPbcV12 K Γ a b c d e).injective
  calc
    (omegaPbcV12 K Γ a b c d e)
        ((E9M K Γ a b c d e ∘ₗ E15M K Γ a b c d e ∘ₗ
          E2M K Γ a b c d e) x)
      = smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
          (pbcTopRoute K Γ a b c d e) (pbcTopDegree K Γ a b c d e)
          (pbcTopRoute_hg K Γ a b c d e)
          ((omegaPbcV2 K Γ a b c d e) x) :=
        LinearMap.congr_fun (facePBC_top K Γ a b c d e) x
    _ = gChiCanon K Γ a (b + c) d e •
          smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
            (pbcBotRoute K Γ a b c d e) (pbcBotDegree K Γ a b c d e)
            (pbcBotRoute_hg K Γ a b c d e)
            ((omegaPbcV2 K Γ a b c d e) x) :=
        LinearMap.congr_fun (pbc_smap_routes K Γ a b c d e)
          ((omegaPbcV2 K Γ a b c d e) x)
    _ = gChiCanon K Γ a (b + c) d e •
          (omegaPbcV12 K Γ a b c d e)
            ((E17M K Γ a b c d e ∘ₗ E16M K Γ a b c d e) x) := by
        have hbot := LinearMap.congr_fun (facePBC_bot K Γ a b c d e) x
        simp only [LinearMap.comp_apply] at hbot
        simp only [LinearMap.comp_apply]
        exact congrArg (fun z => gChiCanon K Γ a (b + c) d e • z) hbot.symm
    _ = (omegaPbcV12 K Γ a b c d e)
          ((gChiCanon K Γ a (b + c) d e •
            (E17M K Γ a b c d e ∘ₗ E16M K Γ a b c d e)) x) := by
        rw [LinearMap.smul_apply, map_smul]

end GaugeChi

end Superfusion
