import RMod.Classification.Instances.FunctorCompositionData
import RMod.Classification.Instances.MonoidalFunctors

/-!
# Laws for identities and composition of superfunctors

Linearity and grading compose directly. Naturality is proved on all
morphisms, including odd ones. Associativity and unit coherence are exactly
Mathlib's composition theorem on the even subcategories, since every
structural comparison in these diagrams is even.
-/

set_option autoImplicit false
universe u₁ v₁ u₂ v₂ u₃ v₃

namespace RMod.Classification

open CategoryTheory Superfusion.Category

namespace SuperfunctorLaws

theorem identity (A : WeaklyPointedSuperfusionData.{u₁, v₁}) :
    SuperfunctorLaws A A (Prefunctor.id A.Obj) where
  map_id _ := rfl
  map_comp _ _ := rfl
  map_zero _ _ := rfl
  map_add _ _ := rfl
  map_smul _ _ := rfl
  map_grade _ h := h

theorem compose {A : WeaklyPointedSuperfusionData.{u₁, v₁}}
    {B : WeaklyPointedSuperfusionData.{u₂, v₂}}
    {C : WeaklyPointedSuperfusionData.{u₃, v₃}}
    {F : SuperfunctorData A B} {G : SuperfunctorData B C}
    (hF : SuperfunctorLaws A B F) (hG : SuperfunctorLaws B C G) :
    SuperfunctorLaws A C (F.comp G) where
  map_id X := by dsimp only [Prefunctor.comp]; rw [hF.map_id, hG.map_id]
  map_comp f g := by dsimp only [Prefunctor.comp]; rw [hF.map_comp, hG.map_comp]
  map_zero X Y := by dsimp only [Prefunctor.comp]; rw [hF.map_zero, hG.map_zero]
  map_add f g := by dsimp only [Prefunctor.comp]; rw [hF.map_add, hG.map_add]
  map_smul r f := by dsimp only [Prefunctor.comp]; rw [hF.map_smul, hG.map_smul]
  map_grade f h := hG.map_grade _ (hF.map_grade f h)

end SuperfunctorLaws

namespace MonoidalSuperfunctorLaws

theorem identity (C : WeaklyPointedSuperfusion.{u₁, v₁}) :
    MonoidalSuperfunctorLaws C.data C.data (MonoidalSuperfunctorData.identity C.data) where
  toSuperfunctorLaws := SuperfunctorLaws.identity C.data
  tensor_hom_even X Y := C.laws.id_even _
  tensor_inv_even X Y := C.laws.id_even _
  tensor_hom_inv X Y := C.laws.comp_id _
  tensor_inv_hom X Y := C.laws.comp_id _
  unit_hom_even := C.laws.id_even _
  unit_inv_even := C.laws.id_even _
  unit_hom_inv := C.laws.comp_id _
  unit_inv_hom := C.laws.comp_id _
  tensor_naturality f g := (C.laws.comp_id _).trans (C.laws.id_comp _).symm
  associativity X Y Z := by
    dsimp only [MonoidalSuperfunctorData.identity, Prefunctor.id]
    rw [C.laws.tensor_id, C.laws.tensor_id, C.laws.comp_id, C.laws.id_comp,
      C.laws.comp_id, C.laws.comp_id]
  left_unit X := by
    dsimp only [MonoidalSuperfunctorData.identity, Prefunctor.id]
    rw [C.laws.tensor_id, C.laws.comp_id, C.laws.id_comp]
  right_unit X := by
    dsimp only [MonoidalSuperfunctorData.identity, Prefunctor.id]
    rw [C.laws.tensor_id, C.laws.comp_id, C.laws.id_comp]

variable {A : WeaklyPointedSuperfusion.{u₁, v₁}}
  {B : WeaklyPointedSuperfusion.{u₂, v₂}}
  {C : WeaklyPointedSuperfusion.{u₃, v₃}}

theorem compose (F : MonoidalSuperfunctor A B) (G : MonoidalSuperfunctor B C) :
    MonoidalSuperfunctorLaws A.data C.data (F.data.compose G.data) where
  toSuperfunctorLaws := F.laws.toSuperfunctorLaws.compose G.laws.toSuperfunctorLaws
  tensor_hom_even X Y := by
    have h := C.laws.comp_grade _ _ (G.laws.tensor_hom_even _ _)
      (G.laws.map_grade _ (F.laws.tensor_hom_even X Y))
    rw [zero_add] at h
    exact h
  tensor_inv_even X Y := by
    have h := C.laws.comp_grade _ _ (G.laws.map_grade _ (F.laws.tensor_inv_even X Y))
      (G.laws.tensor_inv_even _ _)
    rw [zero_add] at h
    exact h
  tensor_hom_inv X Y := by
    dsimp only [MonoidalSuperfunctorData.compose, Prefunctor.comp]
    rw [C.laws.comp_assoc, ← C.laws.comp_assoc (G.data.map _), ← G.laws.map_comp,
      F.laws.tensor_hom_inv, G.laws.map_id, C.laws.id_comp, G.laws.tensor_hom_inv]
  tensor_inv_hom X Y := by
    dsimp only [MonoidalSuperfunctorData.compose, Prefunctor.comp]
    rw [C.laws.comp_assoc, ← C.laws.comp_assoc (G.data.tensorInv _ _),
      G.laws.tensor_inv_hom, C.laws.id_comp, ← G.laws.map_comp,
      F.laws.tensor_inv_hom, G.laws.map_id]
  unit_hom_even := by
    have h := C.laws.comp_grade _ _ G.laws.unit_hom_even
      (G.laws.map_grade _ F.laws.unit_hom_even)
    rw [zero_add] at h
    exact h
  unit_inv_even := by
    have h := C.laws.comp_grade _ _ (G.laws.map_grade _ F.laws.unit_inv_even)
      G.laws.unit_inv_even
    rw [zero_add] at h
    exact h
  unit_hom_inv := by
    dsimp only [MonoidalSuperfunctorData.compose, Prefunctor.comp]
    rw [C.laws.comp_assoc, ← C.laws.comp_assoc (G.data.map _), ← G.laws.map_comp,
      F.laws.unit_hom_inv, G.laws.map_id, C.laws.id_comp, G.laws.unit_hom_inv]
  unit_inv_hom := by
    dsimp only [MonoidalSuperfunctorData.compose, Prefunctor.comp]
    rw [C.laws.comp_assoc, ← C.laws.comp_assoc G.data.unitInv,
      G.laws.unit_inv_hom, C.laws.id_comp, ← G.laws.map_comp,
      F.laws.unit_inv_hom, G.laws.map_id]
  tensor_naturality {X X' Y Y'} f g := by
    dsimp only [MonoidalSuperfunctorData.compose, Prefunctor.comp]
    rw [← C.laws.comp_assoc, G.laws.tensor_naturality, C.laws.comp_assoc,
      ← G.laws.map_comp, F.laws.tensor_naturality, G.laws.map_comp, ← C.laws.comp_assoc]
  associativity X Y Z := by
    let H := F.toSuperfunctor.toEvenFunctor ⋙ G.toSuperfunctor.toEvenFunctor
    have h := congrArg (fun f => f.hom) (Functor.LaxMonoidal.associativity H
      (evenObj ℝ (LinearCategory A) X) (evenObj ℝ (LinearCategory A) Y)
      (evenObj ℝ (LinearCategory A) Z))
    rw [C.laws.comp_assoc, C.laws.comp_assoc]
    exact h
  left_unit X := by
    let H := F.toSuperfunctor.toEvenFunctor ⋙ G.toSuperfunctor.toEvenFunctor
    have h := congrArg (fun f => f.hom) (Functor.LaxMonoidal.left_unitality H
      (evenObj ℝ (LinearCategory A) X))
    rw [C.laws.comp_assoc]
    exact h.symm
  right_unit X := by
    let H := F.toSuperfunctor.toEvenFunctor ⋙ G.toSuperfunctor.toEvenFunctor
    have h := congrArg (fun f => f.hom) (Functor.LaxMonoidal.right_unitality H
      (evenObj ℝ (LinearCategory A) X))
    rw [C.laws.comp_assoc]
    exact h.symm

end MonoidalSuperfunctorLaws

namespace MonoidalSuperfunctor

def identity (C : WeaklyPointedSuperfusion.{u₁, v₁}) : MonoidalSuperfunctor C C :=
  ⟨MonoidalSuperfunctorData.identity C.data, MonoidalSuperfunctorLaws.identity C⟩

def compose {A : WeaklyPointedSuperfusion.{u₁, v₁}}
    {B : WeaklyPointedSuperfusion.{u₂, v₂}} {C : WeaklyPointedSuperfusion.{u₃, v₃}}
    (F : MonoidalSuperfunctor A B) (G : MonoidalSuperfunctor B C) : MonoidalSuperfunctor A C :=
  ⟨F.data.compose G.data, MonoidalSuperfunctorLaws.compose F G⟩

end MonoidalSuperfunctor
end RMod.Classification
