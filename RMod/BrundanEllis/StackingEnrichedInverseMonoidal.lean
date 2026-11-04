import RMod.BrundanEllis.StackingInverseCoreMonoidal
import RMod.BrundanEllis.StackingInverseTensor
import RMod.BrundanEllis.StackingEnrichedUnit

/-! The actual enriched inverse inherits both ordinary coherence and tensor naturality in every degree. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable {C : Type} [SuperCategory C] [MonoidalCategory (Even C)] [MonoidalSuperCategory C]
variable {D : Type} [SuperCategory D] [MonoidalCategory (Even D)] [MonoidalSuperCategory D]
  (F : SuperFunctor C D) (hF : ∀ X Y a, Function.Bijective (F.map X Y a))
  (R : D → C) (e : ∀ X : D, F.forget.obj (evenObj C (R X)) ≅ evenObj D X)

/-- Retain the actual enriched inverse and its counit in the even equivalence. -/
def enrichedInverseEvenEquivalence : Even C ≌ Even D :=
  CategoryTheory.Equivalence.mk F.forget (enrichedInverse F hF R e).forget
    (enrichedInverseUnit F hF R e) (enrichedInverseCounit F hF R e)

/-- The chosen inverse inherits ordinary monoidal coherence. -/
def enrichedInverseCoreMonoidal (M : F.forget.CoreMonoidal) :
    (enrichedInverse F hF R e).forget.CoreMonoidal :=
  inverseCoreMonoidal (enrichedInverseEvenEquivalence F hF R e) M

/-- Ordinary inverse coherence and the full enriched counit give all-degree
naturality for the induced inverse tensorator. -/
theorem enrichedInverse_tensor_natural (M : F.forget.CoreMonoidal)
    (hM : ∀ X X' Y Y' : Even C,
      (F.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec X') ⊗ₘ
        F.map (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Y')) ≫
        KaroubiSuper.ambientTensor (F.forget.obj X) (F.forget.obj X') (F.forget.obj Y) (F.forget.obj Y') ≫
        eHomWhiskerLeft SuperVec (F.forget.obj X ⊗ F.forget.obj Y) (M.μIso X' Y').hom =
      KaroubiSuper.ambientTensor X X' Y Y' ≫
        F.map (ForgetEnrichment.to SuperVec (X ⊗ Y)) (ForgetEnrichment.to SuperVec (X' ⊗ Y')) ≫
        eHomWhiskerRight SuperVec (M.μIso X Y).hom (F.forget.obj (X' ⊗ Y')))
    (X X' Y Y' : Even D) :
    let G := enrichedInverse F hF R e
    (G.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec X') ⊗ₘ
      G.map (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Y')) ≫
      KaroubiSuper.ambientTensor (G.forget.obj X) (G.forget.obj X') (G.forget.obj Y) (G.forget.obj Y') ≫
      eHomWhiskerLeft SuperVec (G.forget.obj X ⊗ G.forget.obj Y)
        ((enrichedInverseCoreMonoidal F hF R e M).μIso X' Y').hom =
    KaroubiSuper.ambientTensor X X' Y Y' ≫
      G.map (ForgetEnrichment.to SuperVec (X ⊗ Y)) (ForgetEnrichment.to SuperVec (X' ⊗ Y')) ≫
      eHomWhiskerRight SuperVec ((enrichedInverseCoreMonoidal F hF R e M).μIso X Y).hom
        (G.forget.obj (X' ⊗ Y')) := by
  apply inverse_tensor_natural F (enrichedInverse F hF R e) hF M.μIso
    (enrichedInverseCoreMonoidal F hF R e M).μIso
    (fun X => e (ForgetEnrichment.to SuperVec X)) hM
  · intro A B
    exact inverseHom_counit F hF R e (ForgetEnrichment.to SuperVec A) (ForgetEnrichment.to SuperVec B)
  · intro A B
    exact inverseCoreMonoidal_tensor_image (enrichedInverseEvenEquivalence F hF R e) M A B

end RMod.BrundanEllis.Stacking
