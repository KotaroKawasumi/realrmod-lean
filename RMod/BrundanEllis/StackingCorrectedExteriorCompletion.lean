import RMod.BrundanEllis.StackingCorrectedExteriorMonoidal
import RMod.BrundanEllis.StackingExternalReversedGeneration
import RMod.BrundanEllis.StackingKaroubiExtensionSuperequivalence

/-! The corrected exterior pairing identifies the completed tensor product
with the external pullback model, conditional on the finite reference
hexagon equations. The comparison acts on all homogeneous morphisms. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
attribute [local irreducible] reversedExteriorPairing correctedExteriorCoreMonoidal

/-- The aligned product tensor differs only by identity transports. -/
theorem product_ambientTensor {A B : Type} [SuperCategory A] [SuperCategory B]
    [MonoidalCategory (Even A)] [MonoidalCategory (Even B)]
    [MonoidalSuperCategory A] [MonoidalSuperCategory B]
    (X X' Y Y' : Even (SuperTensorProduct A B)) :
    KaroubiSuper.ambientTensor X X' Y Y' =
      (productTensor A B).map (X, Y) (X', Y') := by
  change (productTensor A B).map (X, Y) (X', Y') ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The reversed exterior images generate every target object by retracts. -/
theorem reversedExteriorPairing_dense (s t : Twist) (W : Even (exteriorModel s t)) :
    ∃ X : Even (SuperTensorProduct (pullback s) (pullback t)),
      Nonempty (Retract W ((reversedExteriorPairing s t).forget.obj X)) := by
  obtain ⟨X, Y, h⟩ := pairHull_retract (reversedExteriorPairing s t)
    (reversedExteriorPairing_generates s t W)
  exact ⟨evenObj _ (X, Y), h⟩

/-- The chosen ordinary tensorator has the already proved full graded square. -/
theorem correctedExteriorCoreMonoidal_naturality (s t : Twist)
    (hl : ∀ b c d, ReferenceCommutor.LeftEquation b c d)
    (hr : ∀ b c d, ReferenceCommutor.RightEquation b c d)
    (X X' Y Y' : Even (SuperTensorProduct (pullback s) (pullback t))) :
    let F := reversedExteriorPairing s t
    let M := correctedExteriorCoreMonoidal s t hl hr
    (F.map X X' ⊗ₘ F.map Y Y') ≫
      KaroubiSuper.ambientTensor (F.forget.obj X) (F.forget.obj X')
        (F.forget.obj Y) (F.forget.obj Y') ≫
      eHomWhiskerLeft SuperVec (F.forget.obj X ⊗ F.forget.obj Y) (M.μIso X' Y').hom =
    KaroubiSuper.ambientTensor X X' Y Y' ≫
      F.map (X ⊗ Y : Even (SuperTensorProduct (pullback s) (pullback t)))
        (X' ⊗ Y' : Even (SuperTensorProduct (pullback s) (pullback t))) ≫
      eHomWhiskerRight SuperVec (M.μIso X Y).hom (F.forget.obj (X' ⊗ Y')) := by
  dsimp only
  rw [correctedExteriorCoreMonoidal_tensor, correctedExteriorCoreMonoidal_tensor]
  rw [product_ambientTensor]
  exact correctedReversedExteriorTensorIso_enriched_naturality s t X X' Y Y'

/-- Extend the corrected exterior comparison to the completed product. -/
def correctedExteriorCompletionSuperequivalence (s t : Twist)
    (hl : ∀ b c d, ReferenceCommutor.LeftEquation b c d)
    (hr : ∀ b c d, ReferenceCommutor.RightEquation b c d) :
    MonoidalSuperequivalence (PullbackProductCompletion s t) (exteriorModel s t) :=
  KaroubiSuper.extensionSuperequivalence
    (C := SuperTensorProduct (pullback s) (pullback t)) (D := exteriorModel s t)
    (reversedExteriorPairing s t) (reversedExteriorPairing_bijective s t)
    (reversedExteriorPairing_dense s t) (correctedExteriorCoreMonoidal s t hl hr)
    (correctedExteriorCoreMonoidal_naturality s t hl hr)

end RMod.BrundanEllis.Stacking
