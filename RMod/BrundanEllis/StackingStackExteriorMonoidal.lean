import RMod.BrundanEllis.StackingCorrectedExteriorCompletion
import RMod.BrundanEllis.StackingDiagonalRestriction

/-! The completed exterior functor and the actual diagonal inclusion
compose monoidally, with naturality on the entire enriched Hom object. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking

/-- The hull inclusion has identity comparisons on all enriched tensor maps. -/
theorem hullInclusion_enriched_tensor (C : WeaklyPointedFusionPiSuperCat)
    {I : Type} (Z : I → Even C) [ObjectProperty.IsMonoidal (AddPiHull C Z)]
    (X X' Y Y' : Even (HullCategory C Z)) :
    let F := hullInclusion C Z
    let M := hullInclusionMonoidal C Z
    (F.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec X') ⊗ₘ
      F.map (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Y')) ≫
      KaroubiSuper.ambientTensor (F.forget.obj X) (F.forget.obj X') (F.forget.obj Y) (F.forget.obj Y') ≫
      eHomWhiskerLeft SuperVec (F.forget.obj X ⊗ F.forget.obj Y) (M.μIso X' Y').hom =
    KaroubiSuper.ambientTensor X X' Y Y' ≫
      F.map (ForgetEnrichment.to SuperVec (X ⊗ Y)) (ForgetEnrichment.to SuperVec (X' ⊗ Y')) ≫
      eHomWhiskerRight SuperVec (M.μIso X Y).hom (F.forget.obj (X' ⊗ Y')) := by
  change (𝟙 _ ⊗ₘ 𝟙 _) ≫ KaroubiSuper.ambientTensor X.obj X'.obj Y.obj Y'.obj ≫
      eHomWhiskerLeft (C := Even C) SuperVec (X.obj ⊗ Y.obj) (𝟙 (X'.obj ⊗ Y'.obj)) =
    KaroubiSuper.ambientTensor X X' Y Y' ≫ 𝟙 _ ≫
      eHomWhiskerRight (C := Even C) SuperVec (𝟙 (X.obj ⊗ Y.obj)) (X'.obj ⊗ Y'.obj)
  simp only [id_tensorHom_id, Category.id_comp, eHomWhiskerLeft_id,
    eHomWhiskerRight_id, Category.comp_id]
  rfl

/-- The public stack inclusion retains this full tensor compatibility. -/
theorem stackInclusion_enriched_tensor (s t : Twist) (h : s.group = t.group)
    (X X' Y Y' : Even (stack s t h)) :
    let F := stackInclusion s t h
    let M := stackMonoidal s t h
    (F.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec X') ⊗ₘ
      F.map (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Y')) ≫
      KaroubiSuper.ambientTensor (F.forget.obj X) (F.forget.obj X') (F.forget.obj Y) (F.forget.obj Y') ≫
      eHomWhiskerLeft SuperVec (F.forget.obj X ⊗ F.forget.obj Y) (M.μIso X' Y').hom =
    KaroubiSuper.ambientTensor X X' Y Y' ≫
      F.map (ForgetEnrichment.to SuperVec (X ⊗ Y)) (ForgetEnrichment.to SuperVec (X' ⊗ Y')) ≫
      eHomWhiskerRight SuperVec (M.μIso X Y).hom (F.forget.obj (X' ⊗ Y')) := by
  letI := diagonalIsMonoidal s t (groupEqualityMulEquiv h)
    (deligne (pullback s) (pullback t)) (delignePairing (pullback s) (pullback t))
    (deligneMonoidal (pullback s) (pullback t))
  exact hullInclusion_enriched_tensor _ _ X X' Y Y'

variable (s t : Twist)
  (hl : ∀ b c d, ReferenceCommutor.LeftEquation b c d)
  (hr : ∀ b c d, ReferenceCommutor.RightEquation b c d)

/-- Extend the corrected exterior monoidal structure to the actual Deligne functor. -/
def reversedDeligneMonoidal : (reversedDeligneFunctor s t).forget.CoreMonoidal :=
  KaroubiSuper.extensionMonoidal (reversedExteriorPairing s t) (correctedExteriorCoreMonoidal s t hl hr)

/-- The completed comparison retains the full graded naturality already proved before completion. -/
theorem reversedDeligneMonoidal_enriched (X X' Y Y' : Even (deligne (pullback s) (pullback t))) :
    let F := reversedDeligneFunctor s t
    let M := reversedDeligneMonoidal s t hl hr
    (F.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec X') ⊗ₘ
      F.map (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Y')) ≫
      KaroubiSuper.ambientTensor (F.forget.obj X) (F.forget.obj X') (F.forget.obj Y) (F.forget.obj Y') ≫
      eHomWhiskerLeft SuperVec (F.forget.obj X ⊗ F.forget.obj Y) (M.μIso X' Y').hom =
    KaroubiSuper.ambientTensor X X' Y Y' ≫
      F.map (ForgetEnrichment.to SuperVec (X ⊗ Y)) (ForgetEnrichment.to SuperVec (X' ⊗ Y')) ≫
      eHomWhiskerRight SuperVec (M.μIso X Y).hom (F.forget.obj (X' ⊗ Y')) :=
  KaroubiSuper.extension_tensor_natural (reversedExteriorPairing s t)
    (correctedExteriorCoreMonoidal s t hl hr) (correctedExteriorCoreMonoidal_naturality s t hl hr)
    X X' Y Y'

/-- Include the diagonal stack and apply the corrected completed exterior comparison. -/
def stackExteriorMonoidal (h : s.group = t.group) : (stackExteriorFunctor s t h).forget.CoreMonoidal :=
  compositeCoreMonoidal (stackInclusion s t h) (reversedDeligneFunctor s t)
    (stackMonoidal s t h) (reversedDeligneMonoidal s t hl hr)

theorem stackExteriorMonoidal_enriched (h : s.group = t.group) (X X' Y Y' : Even (stack s t h)) :
    let F := stackExteriorFunctor s t h
    let M := stackExteriorMonoidal s t hl hr h
    (F.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec X') ⊗ₘ
      F.map (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Y')) ≫
      KaroubiSuper.ambientTensor (F.forget.obj X) (F.forget.obj X') (F.forget.obj Y) (F.forget.obj Y') ≫
      eHomWhiskerLeft SuperVec (F.forget.obj X ⊗ F.forget.obj Y) (M.μIso X' Y').hom =
    KaroubiSuper.ambientTensor X X' Y Y' ≫
      F.map (ForgetEnrichment.to SuperVec (X ⊗ Y)) (ForgetEnrichment.to SuperVec (X' ⊗ Y')) ≫
      eHomWhiskerRight SuperVec (M.μIso X Y).hom (F.forget.obj (X' ⊗ Y')) :=
  composite_tensor_natural (stackInclusion s t h) (reversedDeligneFunctor s t)
    (stackMonoidal s t h) (reversedDeligneMonoidal s t hl hr)
    (stackInclusion_enriched_tensor s t h) (reversedDeligneMonoidal_enriched s t hl hr) X X' Y Y'

end RMod.BrundanEllis.Stacking
