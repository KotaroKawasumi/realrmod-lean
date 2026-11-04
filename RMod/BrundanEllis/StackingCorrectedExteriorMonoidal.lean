import RMod.BrundanEllis.StackingCorrectedExteriorAssociativity
import RMod.BrundanEllis.StackingSemigroupalUnit
import RMod.BrundanEllis.StackingCorrectedExteriorNaturality
import RMod.BrundanEllis.StackingExternalReversedUnit
import RMod.BrundanEllis.StackingEvenNaturality
import RMod.BrundanEllis.StackingProductPure

/-! Coherence of the corrected exterior tensor comparison and normalization of its unit. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace RMod.BrundanEllis.Stacking
open CategoryTheory CategoryTheory.MonoidalCategory
attribute [local irreducible] reversedExteriorPairing correctedReversedExteriorTensorIso

set_option maxHeartbeats 400000 in
/-- Evaluating the full graded naturality equation at even input maps
gives the ordinary naturality required by CoreMonoidal. -/
theorem correctedReversedExteriorTensorIso_even_naturality (s t : Twist)
    {X X' Y Y' : Even (SuperTensorProduct (pullback s) (pullback t))}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    let F := (reversedExteriorPairing s t).forget
    (F.map f ⊗ₘ F.map g) ≫ (correctedReversedExteriorTensorIso s t X' Y').hom =
      (correctedReversedExteriorTensorIso s t X Y).hom ≫ F.map (f ⊗ₘ g) := by
  dsimp only
  apply (eHomEquiv SuperVec).injective
  rw [← even_post, ← even_pre]
  change ForgetEnrichment.homTo SuperVec
      ((reversedExteriorPairing s t).forget.map f ⊗ₘ (reversedExteriorPairing s t).forget.map g) ≫ _ =
    ForgetEnrichment.homTo SuperVec ((reversedExteriorPairing s t).forget.map (f ⊗ₘ g)) ≫ _
  rw [← MonoidalSuperCategory.tensor_even]
  simp only [Category.assoc]
  change (λ_ (𝟙_ SuperVec)).inv ≫
      ((ForgetEnrichment.homTo SuperVec f ≫ (reversedExteriorPairing s t).map X X') ⊗ₘ
       (ForgetEnrichment.homTo SuperVec g ≫ (reversedExteriorPairing s t).map Y Y')) ≫ _ =
    (ForgetEnrichment.homTo SuperVec (f ⊗ₘ g) ≫
      (reversedExteriorPairing s t).map
        (X ⊗ Y : Even (SuperTensorProduct (pullback s) (pullback t)))
        (X' ⊗ Y' : Even (SuperTensorProduct (pullback s) (pullback t)))) ≫ _
  rw [← tensorHom_comp_tensorHom, product_tensor_homTo]
  simp only [Category.assoc]
  exact congrArg (fun z => (λ_ (𝟙_ SuperVec)).inv ≫
    (ForgetEnrichment.homTo SuperVec f ⊗ₘ ForgetEnrichment.homTo SuperVec g) ≫ z)
    (correctedReversedExteriorTensorIso_enriched_naturality s t X X' Y Y')

set_option maxHeartbeats 400000 in
/-- The actual exterior functor is strong monoidal, conditional only on
the concrete finite reference hexagon certificates. The unit comparison
is normalized from the existing unit object isomorphism. -/
def correctedExteriorCoreMonoidal (s t : Twist)
    (hl : ∀ b c d, ReferenceCommutor.LeftEquation b c d)
    (hr : ∀ b c d, ReferenceCommutor.RightEquation b c d) :
    (reversedExteriorPairing s t).forget.CoreMonoidal :=
  coreMonoidalOfAssociativity (reversedExteriorPairing s t).forget
    (correctedReversedExteriorTensorIso s t) (reversedExteriorUnitIso s t)
    (by
      intro X Y f Z
      have hn := correctedReversedExteriorTensorIso_even_naturality s t f (𝟙 Z)
      dsimp only at hn
      rw [CategoryTheory.Functor.map_id, tensorHom_id] at hn
      exact hn)
    (by
      intro X Y Z f
      have hn := correctedReversedExteriorTensorIso_even_naturality s t (𝟙 Z) f
      dsimp only at hn
      rw [CategoryTheory.Functor.map_id, id_tensorHom] at hn
      exact hn)
    (correctedReversedExteriorTensorIso_associativity s t hl hr)

/-- Normalizing the unit leaves the specified binary comparisons intact. -/
theorem correctedExteriorCoreMonoidal_tensor (s t : Twist)
    (hl : ∀ b c d, ReferenceCommutor.LeftEquation b c d)
    (hr : ∀ b c d, ReferenceCommutor.RightEquation b c d)
    (X Y : Even (SuperTensorProduct (pullback s) (pullback t))) :
    (correctedExteriorCoreMonoidal s t hl hr).μIso X Y =
      correctedReversedExteriorTensorIso s t X Y := rfl

end RMod.BrundanEllis.Stacking
