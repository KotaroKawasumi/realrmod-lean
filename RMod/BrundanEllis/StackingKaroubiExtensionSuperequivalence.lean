import RMod.BrundanEllis.StackingKaroubiExtensionTensor
import RMod.BrundanEllis.StackingMonoidalComparison

/-! A fully faithful enriched monoidal functor extends to a monoidal
superequivalence when every target object is a retract of its image.
The total-morphism naturality lemma keeps this construction opaque to
elaboration instead of expanding the chosen splitting of every corner. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable {C D : Type} [SuperCategory C] [SuperCategory D]
  [IsIdempotentComplete (Even D)]

/-- The fixed completed functor is an ordinary equivalence. -/
theorem extension_isEquivalence (F : SuperFunctor C D)
    (hF : ∀ X Y a, Function.Bijective (F.map X Y a))
    (hR : ∀ W : Even D, ∃ X : Even C, Nonempty (Retract W (F.forget.obj X))) :
    (extension F).forget.IsEquivalence :=
  (extensionEquivalence F hF hR).isEquivalence_functor

variable [MonoidalCategory (Even C)] [MonoidalCategory (Even D)]
  [MonoidalSuperCategory C] [MonoidalSuperCategory D]

/-- The completed tensorator is natural on arbitrary total morphisms. -/
theorem extension_tensor_total (F : SuperFunctor C D) (M : F.forget.CoreMonoidal)
    (hM : ∀ X X' Y Y' : Even C,
      (F.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec X') ⊗ₘ
        F.map (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Y')) ≫
        ambientTensor (F.forget.obj X) (F.forget.obj X') (F.forget.obj Y) (F.forget.obj Y') ≫
        eHomWhiskerLeft SuperVec (F.forget.obj X ⊗ F.forget.obj Y) (M.μIso X' Y').hom =
      ambientTensor X X' Y Y' ≫ F.map (ForgetEnrichment.to SuperVec (X ⊗ Y))
        (ForgetEnrichment.to SuperVec (X' ⊗ Y')) ≫
        eHomWhiskerRight SuperVec (M.μIso X Y).hom (F.forget.obj (X' ⊗ Y')))
    {X X' Y Y' : Even (Karoubi (Even C))}
    (f : THom (Karoubi (Even C)) X X') (g : THom (Karoubi (Even C)) Y Y') :
    tComp D (tTensor (C := D) MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects
      (tMap (extension F) f) (tMap (extension F) g))
      (evenPoint ((extensionMonoidal F M).μIso X' Y').hom) =
    tComp D (evenPoint ((extensionMonoidal F M).μIso X Y).hom)
      (tMap (extension F) (tTensor (C := Karoubi (Even C)) MonoidalSuperCategory.tensor
        MonoidalSuperCategory.tensor_objects f g)) := by
  exact tensor_naturality_total (extension F) (extensionMonoidal F M)
    (fun A A' B B' => extension_tensor_natural F M hM A A' B B') f g

/-- Extend a fully faithful graded monoidal functor whose image generates
under retracts to a monoidal superequivalence of the completion. -/
def extensionSuperequivalence (F : SuperFunctor C D)
    (hF : ∀ X Y a, Function.Bijective (F.map X Y a))
    (hR : ∀ W : Even D, ∃ X : Even C, Nonempty (Retract W (F.forget.obj X)))
    (M : F.forget.CoreMonoidal)
    (hM : ∀ X X' Y Y' : Even C,
      (F.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec X') ⊗ₘ
        F.map (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Y')) ≫
        ambientTensor (F.forget.obj X) (F.forget.obj X') (F.forget.obj Y) (F.forget.obj Y') ≫
        eHomWhiskerLeft SuperVec (F.forget.obj X ⊗ F.forget.obj Y) (M.μIso X' Y').hom =
      ambientTensor X X' Y Y' ≫ F.map (ForgetEnrichment.to SuperVec (X ⊗ Y))
        (ForgetEnrichment.to SuperVec (X' ⊗ Y')) ≫
        eHomWhiskerRight SuperVec (M.μIso X Y).hom (F.forget.obj (X' ⊗ Y')))
    : MonoidalSuperequivalence (Karoubi (Even C)) D := by
  letI : (extension F).forget.IsEquivalence := extension_isEquivalence F hF hR
  exact monoidalSuperequivalenceOfFullyFaithful
    (C := Karoubi (Even C)) (D := D) (extension F) (extensionMonoidal F M)
    (extension_bijective F hF)
    (fun f g => extension_tensor_total F M hM f g)

end RMod.BrundanEllis.Stacking.KaroubiSuper
