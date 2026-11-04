import RMod.Classification.Instances.Functors
import RMod.Classification.Instances.LinearMonoidal
import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Strong monoidal functors on the even subcategories

The specified even tensorators and unit maps define Mathlib's core monoidal
structure. Its ordinary coherence results can consequently be reused for
composition. Naturality on odd morphisms remains part of the original
superfunctor laws and is checked separately in subsequent constructions.
-/

set_option autoImplicit false
universe u₁ v₁ u₂ v₂

namespace RMod.Classification.MonoidalSuperfunctor

open CategoryTheory Superfusion.Category

variable {C : WeaklyPointedSuperfusion.{u₁, v₁}}
  {D : WeaklyPointedSuperfusion.{u₂, v₂}}

def toSuperfunctor (F : MonoidalSuperfunctor C D) : Superfunctor C D :=
  ⟨F.data.toPrefunctor, F.laws.toSuperfunctorLaws⟩

def evenCoreMonoidal (F : MonoidalSuperfunctor C D) :
    F.toSuperfunctor.toEvenFunctor.CoreMonoidal where
  εIso :=
    { hom := ⟨F.data.unitHom, F.laws.unit_hom_even⟩
      inv := ⟨F.data.unitInv, F.laws.unit_inv_even⟩
      hom_inv_id := WideSubcategory.hom_ext _ F.laws.unit_hom_inv
      inv_hom_id := WideSubcategory.hom_ext _ F.laws.unit_inv_hom }
  μIso X Y :=
    { hom := ⟨F.data.tensorHom X.obj Y.obj, F.laws.tensor_hom_even X.obj Y.obj⟩
      inv := ⟨F.data.tensorInv X.obj Y.obj, F.laws.tensor_inv_even X.obj Y.obj⟩
      hom_inv_id := WideSubcategory.hom_ext _ (F.laws.tensor_hom_inv X.obj Y.obj)
      inv_hom_id := WideSubcategory.hom_ext _ (F.laws.tensor_inv_hom X.obj Y.obj) }
  μIso_hom_natural_left {X Y} f Z := by
    apply WideSubcategory.hom_ext
    have h := F.laws.tensor_naturality f.hom (C.data.id Z.obj)
    rw [F.laws.map_id] at h
    exact h
  μIso_hom_natural_right {X Y} Z f := by
    apply WideSubcategory.hom_ext
    have h := F.laws.tensor_naturality (C.data.id Z.obj) f.hom
    rw [F.laws.map_id] at h
    exact h
  associativity X Y Z := by
    apply WideSubcategory.hom_ext
    have h := F.laws.associativity X.obj Y.obj Z.obj
    simp only [D.laws.comp_assoc] at h
    exact h
  left_unitality X := by
    apply WideSubcategory.hom_ext
    have h := F.laws.left_unit X.obj
    rw [D.laws.comp_assoc] at h
    exact h.symm
  right_unitality X := by
    apply WideSubcategory.hom_ext
    have h := F.laws.right_unit X.obj
    rw [D.laws.comp_assoc] at h
    exact h.symm

noncomputable instance evenMonoidal (F : MonoidalSuperfunctor C D) :
    F.toSuperfunctor.toEvenFunctor.Monoidal :=
  F.evenCoreMonoidal.toMonoidal

end RMod.Classification.MonoidalSuperfunctor
