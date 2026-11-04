import RMod.Classification.Proofs.FunctorComposition

/-!
# Composition of completed monoidal superequivalences

The unit of a composite passes through the inner unit and then the inverse
functor image of the outer unit; the counit follows the dual route. The
specified inverses and their evenness are retained. These constructions
give reflexivity and transitivity for the public relation on completed
Pi-superfusion categories.
-/

set_option autoImplicit false
universe u₁ v₁ u₂ v₂ u₃ v₃

namespace RMod.Classification

namespace MonoidalSuperequivalenceLaws

theorem identity (C : WeaklyPointedSuperfusion.{u₁, v₁}) :
    MonoidalSuperequivalenceLaws C.data C.data
      (MonoidalSuperequivalenceData.identity C.data) where
  forward := MonoidalSuperfunctorLaws.identity C
  backward := SuperfunctorLaws.identity C.data
  unit_hom_even := C.laws.id_even
  unit_inv_even := C.laws.id_even
  unit_hom_inv _ := C.laws.comp_id _
  unit_inv_hom _ := C.laws.comp_id _
  counit_hom_even := C.laws.id_even
  counit_inv_even := C.laws.id_even
  counit_hom_inv _ := C.laws.comp_id _
  counit_inv_hom _ := C.laws.comp_id _
  unit_naturality f := (C.laws.comp_id f).trans (C.laws.id_comp f).symm
  counit_naturality f := (C.laws.comp_id f).trans (C.laws.id_comp f).symm

variable {A : WeaklyPointedSuperfusion.{u₁, v₁}}
  {B : WeaklyPointedSuperfusion.{u₂, v₂}}
  {C : WeaklyPointedSuperfusion.{u₃, v₃}}

theorem compose (E : MonoidalSuperequivalence A B) (F : MonoidalSuperequivalence B C) :
    MonoidalSuperequivalenceLaws A.data C.data (E.data.compose F.data) where
  forward := MonoidalSuperfunctorLaws.compose
    ⟨E.data.forward, E.laws.forward⟩ ⟨F.data.forward, F.laws.forward⟩
  backward := F.laws.backward.compose E.laws.backward
  unit_hom_even X := by
    have h := A.laws.comp_grade _ _ (E.laws.unit_hom_even X)
      (E.laws.backward.map_grade _ (F.laws.unit_hom_even _))
    rw [zero_add] at h
    exact h
  unit_inv_even X := by
    have h := A.laws.comp_grade _ _
      (E.laws.backward.map_grade _ (F.laws.unit_inv_even _)) (E.laws.unit_inv_even X)
    rw [zero_add] at h
    exact h
  unit_hom_inv X := by
    dsimp only [MonoidalSuperequivalenceData.compose, MonoidalSuperfunctorData.compose,
      Prefunctor.comp]
    rw [A.laws.comp_assoc, ← A.laws.comp_assoc (E.data.backward.map _),
      ← E.laws.backward.map_comp, F.laws.unit_hom_inv, E.laws.backward.map_id,
      A.laws.id_comp, E.laws.unit_hom_inv]
  unit_inv_hom X := by
    dsimp only [MonoidalSuperequivalenceData.compose, MonoidalSuperfunctorData.compose,
      Prefunctor.comp]
    rw [A.laws.comp_assoc, ← A.laws.comp_assoc (E.data.unitInv _),
      E.laws.unit_inv_hom, A.laws.id_comp, ← E.laws.backward.map_comp,
      F.laws.unit_inv_hom, E.laws.backward.map_id]
  counit_hom_even Y := by
    have h := C.laws.comp_grade _ _
      (F.laws.forward.map_grade _ (E.laws.counit_hom_even _)) (F.laws.counit_hom_even Y)
    rw [zero_add] at h
    exact h
  counit_inv_even Y := by
    have h := C.laws.comp_grade _ _ (F.laws.counit_inv_even Y)
      (F.laws.forward.map_grade _ (E.laws.counit_inv_even _))
    rw [zero_add] at h
    exact h
  counit_hom_inv Y := by
    dsimp only [MonoidalSuperequivalenceData.compose, MonoidalSuperfunctorData.compose,
      Prefunctor.comp]
    rw [C.laws.comp_assoc, ← C.laws.comp_assoc (F.data.counitHom _),
      F.laws.counit_hom_inv, C.laws.id_comp, ← F.laws.forward.map_comp,
      E.laws.counit_hom_inv, F.laws.forward.map_id]
  counit_inv_hom Y := by
    dsimp only [MonoidalSuperequivalenceData.compose, MonoidalSuperfunctorData.compose,
      Prefunctor.comp]
    rw [C.laws.comp_assoc, ← C.laws.comp_assoc (F.data.forward.map _),
      ← F.laws.forward.map_comp, E.laws.counit_inv_hom, F.laws.forward.map_id,
      C.laws.id_comp, F.laws.counit_inv_hom]
  unit_naturality f := by
    dsimp only [MonoidalSuperequivalenceData.compose, MonoidalSuperfunctorData.compose,
      Prefunctor.comp]
    rw [← A.laws.comp_assoc, E.laws.unit_naturality, A.laws.comp_assoc,
      ← E.laws.backward.map_comp, F.laws.unit_naturality,
      E.laws.backward.map_comp, ← A.laws.comp_assoc]
  counit_naturality f := by
    dsimp only [MonoidalSuperequivalenceData.compose, MonoidalSuperfunctorData.compose,
      Prefunctor.comp]
    rw [← C.laws.comp_assoc, ← F.laws.forward.map_comp, E.laws.counit_naturality,
      F.laws.forward.map_comp, C.laws.comp_assoc, F.laws.counit_naturality,
      ← C.laws.comp_assoc]

end MonoidalSuperequivalenceLaws

namespace MonoidalSuperequivalence

def identity (C : WeaklyPointedSuperfusion.{u₁, v₁}) : MonoidalSuperequivalence C C :=
  ⟨MonoidalSuperequivalenceData.identity C.data, MonoidalSuperequivalenceLaws.identity C⟩

def compose {A : WeaklyPointedSuperfusion.{u₁, v₁}}
    {B : WeaklyPointedSuperfusion.{u₂, v₂}} {C : WeaklyPointedSuperfusion.{u₃, v₃}}
    (E : MonoidalSuperequivalence A B) (F : MonoidalSuperequivalence B C) :
    MonoidalSuperequivalence A C :=
  ⟨E.data.compose F.data, MonoidalSuperequivalenceLaws.compose E F⟩

end MonoidalSuperequivalence

theorem Equivalent.refl (C : PiSuperfusion.{u₁, v₁}) : Equivalent C C :=
  ⟨MonoidalSuperequivalence.identity C.toWeaklyPointedSuperfusion⟩

theorem Equivalent.trans {A : PiSuperfusion.{u₁, v₁}}
    {B : PiSuperfusion.{u₂, v₂}} {C : PiSuperfusion.{u₃, v₃}}
    (hAB : Equivalent A B) (hBC : Equivalent B C) : Equivalent A C := by
  obtain ⟨E⟩ := hAB
  obtain ⟨F⟩ := hBC
  exact ⟨E.compose F⟩

end RMod.Classification
