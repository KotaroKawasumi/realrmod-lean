import RMod.Classification.Abstract.Equivalence
import RMod.Classification.Instances.EndGrading
import Superfusion.Category.Even
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Equivalence

/-!
# Mathlib functors underlying superfunctors

The object and morphism maps are exactly the maps in the separated data.
The supplied laws give ordinary real-linear functors on all morphisms and
on the even subcategories. Even unit and counit maps give an equivalence
of the latter categories as well. Mathlib's equivalence constructor supplies
the triangle identity by adjointification; no extra triangle is assumed.
-/

set_option autoImplicit false
universe u₁ v₁ u₂ v₂

namespace RMod.Classification

open CategoryTheory Superfusion.Category

variable {C : WeaklyPointedSuperfusion.{u₁, v₁}}
  {D : WeaklyPointedSuperfusion.{u₂, v₂}}

namespace Superfunctor

def toFunctor (F : Superfunctor C D) : LinearCategory C ⥤ LinearCategory D where
  obj := F.data.obj
  map := F.data.map
  map_id := F.laws.map_id
  map_comp := F.laws.map_comp

instance additive (F : Superfunctor C D) : F.toFunctor.Additive where
  map_add := F.laws.map_add _ _

instance linear (F : Superfunctor C D) : F.toFunctor.Linear ℝ where
  map_smul f r := F.laws.map_smul r f

/-- Restriction uses Mathlib's existing wide subcategory of even maps. -/
def toEvenFunctor (F : Superfunctor C D) :
    EvenSubcategory ℝ (LinearCategory C) ⥤ EvenSubcategory ℝ (LinearCategory D) where
  obj X := ⟨F.data.obj X.obj⟩
  map f := ⟨F.data.map f.hom, F.laws.map_grade _ f.property⟩
  map_id X := by
    apply WideSubcategory.hom_ext
    exact F.laws.map_id X.obj
  map_comp f g := by
    apply WideSubcategory.hom_ext
    exact F.laws.map_comp f.hom g.hom

instance evenAdditive (F : Superfunctor C D) : F.toEvenFunctor.Additive where
  map_add := by
    intro X Y f g
    apply WideSubcategory.hom_ext
    exact F.laws.map_add f.hom g.hom

instance evenLinear (F : Superfunctor C D) : F.toEvenFunctor.Linear ℝ where
  map_smul f r := by
    apply WideSubcategory.hom_ext
    exact F.laws.map_smul r f.hom

end Superfunctor

namespace MonoidalSuperequivalence

def forwardFunctor (E : MonoidalSuperequivalence C D) : Superfunctor C D :=
  ⟨E.data.forward.toPrefunctor, E.laws.forward.toSuperfunctorLaws⟩

def backwardFunctor (E : MonoidalSuperequivalence C D) : Superfunctor D C :=
  ⟨E.data.backward, E.laws.backward⟩

/-- Both natural isomorphisms are those explicitly specified by the data. -/
def underlyingEquivalence (E : MonoidalSuperequivalence C D) :
    LinearCategory C ≌ LinearCategory D :=
  CategoryTheory.Equivalence.mk E.forwardFunctor.toFunctor E.backwardFunctor.toFunctor
    (NatIso.ofComponents
      (fun X =>
        { hom := E.data.unitHom X
          inv := E.data.unitInv X
          hom_inv_id := E.laws.unit_hom_inv X
          inv_hom_id := E.laws.unit_inv_hom X })
      (fun f => E.laws.unit_naturality f))
    (NatIso.ofComponents
      (fun Y =>
        { hom := E.data.counitHom Y
          inv := E.data.counitInv Y
          hom_inv_id := E.laws.counit_hom_inv Y
          inv_hom_id := E.laws.counit_inv_hom Y })
      (fun f => E.laws.counit_naturality f))

def evenEquivalence (E : MonoidalSuperequivalence C D) :
    EvenSubcategory ℝ (LinearCategory C) ≌ EvenSubcategory ℝ (LinearCategory D) :=
  CategoryTheory.Equivalence.mk E.forwardFunctor.toEvenFunctor E.backwardFunctor.toEvenFunctor
    (NatIso.ofComponents
      (fun X =>
        { hom := ⟨E.data.unitHom X.obj, E.laws.unit_hom_even X.obj⟩
          inv := ⟨E.data.unitInv X.obj, E.laws.unit_inv_even X.obj⟩
          hom_inv_id := WideSubcategory.hom_ext _ (E.laws.unit_hom_inv X.obj)
          inv_hom_id := WideSubcategory.hom_ext _ (E.laws.unit_inv_hom X.obj) })
      (fun f => WideSubcategory.hom_ext _ (E.laws.unit_naturality f.hom)))
    (NatIso.ofComponents
      (fun Y =>
        { hom := ⟨E.data.counitHom Y.obj, E.laws.counit_hom_even Y.obj⟩
          inv := ⟨E.data.counitInv Y.obj, E.laws.counit_inv_even Y.obj⟩
          hom_inv_id := WideSubcategory.hom_ext _ (E.laws.counit_hom_inv Y.obj)
          inv_hom_id := WideSubcategory.hom_ext _ (E.laws.counit_inv_hom Y.obj) })
      (fun f => WideSubcategory.hom_ext _ (E.laws.counit_naturality f.hom)))

end MonoidalSuperequivalence
end RMod.Classification
