import RMod.Hierarchy.Bridge.TotalHom

/-!
# The old category and endomorphism algebras are preserved

The reconstruction of total Hom spaces is fully faithful and keeps every
object. Its endomorphism equivalence is an algebra equivalence, including
the composition order used by Mathlib's `End`.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory
namespace RMod.Legacy.Hierarchy
variable (C : WeaklyPointedSuperfusion.{0, 0})

def totalForget : TotalCategory (ofOldSupercategory C) ⥤ Classification.LinearCategory C where
  obj X := X
  map {X Y} f := totalHomEquiv C X Y f
  map_id X := totalHomEquiv_id C X
  map_comp f g := totalHomEquiv_comp C _ _ _ f g

instance totalForget_faithful : (totalForget C).Faithful where
  map_injective {X Y} {_ _} h := (totalHomEquiv C X Y).injective h

instance totalForget_full : (totalForget C).Full where
  map_surjective := (totalHomEquiv C _ _).surjective

instance totalForget_essSurj : (totalForget C).EssSurj where
  mem_essImage Y := ⟨Y, ⟨Iso.refl Y⟩⟩

instance totalForget_isEquivalence : (totalForget C).IsEquivalence where

def totalEquivalence : TotalCategory (ofOldSupercategory C) ≌ Classification.LinearCategory C :=
  (totalForget C).asEquivalence

def totalEndEquiv (X : Classification.LinearCategory C) :
    End (totalObj (ofOldSupercategory C) X) ≃ₐ[ℝ] End X :=
  AlgEquiv.ofLinearEquiv (totalHomEquiv C X X) (totalHomEquiv_id C X)
    (fun f g => totalHomEquiv_comp C X X X g f)

end RMod.Legacy.Hierarchy
