import RMod.Hierarchy.Instances.EquivalenceFunctors

/-!
# Composition of monoidal superequivalences

Mathlib composes the even comparison isomorphisms and their coherence.
The total naturality identities follow by functoriality and associativity.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.Legacy

theorem evenPoint_category_comp (C : Supercategory) {X Y Z : Even C}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    evenPoint (@CategoryStruct.comp (Even C) inferInstance X Y Z f g) =
      tComp C.data (evenPoint f) (evenPoint g) := evenPoint_comp C.data f g

theorem evenPoint_functor_map {C D : Supercategory} (F : Superfunctor C D)
    {X Y : Even C} (f : X ⟶ Y) :
    evenPoint (F.enriched.forget.map f) = tMap F.data (evenPoint f) := (tMap_evenPoint F f).symm

theorem superfunctor_comp_even_map {A B C : Supercategory}
    (F : Superfunctor A B) (G : Superfunctor B C) {X Y : Even A} (f : X ⟶ Y) :
    (F.comp G).enriched.forget.map f = G.enriched.forget.map (F.enriched.forget.map f) := by
  exact (@Category.assoc SuperVec inferInstance (𝟙_ SuperVec)
    (A.data.Hom X Y) (B.data.Hom (F.data.obj X) (F.data.obj Y))
    (C.data.Hom (G.data.obj (F.data.obj X)) (G.data.obj (F.data.obj Y)))
    f (F.data.map X Y) (G.data.map _ _)).symm

namespace MonoidalSuperequivalence
variable {A B C : MonoidalSupercategory}
  (E : MonoidalSuperequivalence A B) (F : MonoidalSuperequivalence B C)

def compData : MonoidalSuperequivalenceData A C where
  forward := (E.forward.comp F.forward).data
  backward := (F.backward.comp E.backward).data
  tensorIso X Y := (F.data.tensorIso (E.evenForward.obj X) (E.evenForward.obj Y)) ≪≫
    F.evenForward.mapIso (E.data.tensorIso X Y)
  unitIso := F.data.unitIso ≪≫ F.evenForward.mapIso E.data.unitIso
  unit X := E.data.unit X ≪≫ E.evenBackward.mapIso (F.data.unit (E.evenForward.obj X))
  counit X := F.evenForward.mapIso (E.data.counit (F.evenBackward.obj X)) ≪≫ F.data.counit X

theorem compLaws : MonoidalSuperequivalenceLaws (compData E F) where
  forward := (E.forward.comp F.forward).laws
  backward := (F.backward.comp E.backward).laws
  unit_natural f := by
    dsimp only [compData, Iso.trans_hom, Functor.mapIso_hom]
    erw [evenPoint_category_comp A.super, evenPoint_category_comp A.super,
      evenPoint_functor_map E.backward, evenPoint_functor_map E.backward,
      tMap_comp_functor, tMap_comp_functor]
    simp only [tMap_comp_functor]
    erw [← tComp_assoc, E.laws.unit_natural, tComp_assoc,
      ← tMap_comp E.backward, F.laws.unit_natural, tMap_comp E.backward, ← tComp_assoc]
    rfl
  counit_natural f := by
    dsimp only [compData, Iso.trans_hom, Functor.mapIso_hom]
    erw [evenPoint_category_comp C.super, evenPoint_category_comp C.super,
      evenPoint_functor_map F.forward, evenPoint_functor_map F.forward,
      tMap_comp_functor, tMap_comp_functor]
    simp only [tMap_comp_functor]
    erw [← tComp_assoc, ← tMap_comp F.forward, E.laws.counit_natural,
      tMap_comp F.forward, tComp_assoc, F.laws.counit_natural, ← tComp_assoc]
    rfl
  tensor_natural f g := by
    dsimp only [compData, Iso.trans_hom, Functor.mapIso_hom]
    erw [evenPoint_category_comp C.super, evenPoint_category_comp C.super,
      evenPoint_functor_map F.forward, evenPoint_functor_map F.forward, tMap_comp_functor, tMap_comp_functor,
      tMap_comp_functor]
    simp only [tMap_comp_functor]
    erw [← tComp_assoc, F.laws.tensor_natural, tComp_assoc,
      ← tMap_comp F.forward, E.laws.tensor_natural, tMap_comp F.forward, ← tComp_assoc]
    rfl
  associativity X Y Z := by
    have h := Functor.LaxMonoidal.associativity (E.evenForward ⋙ F.evenForward) X Y Z
    change _ = _ at h
    change _ ≫ _ ≫ (E.forward.comp F.forward).enriched.forget.map (α_ X Y Z).hom = _
    rw [superfunctor_comp_even_map]
    exact h
  left_unit X := by
    have h := Functor.LaxMonoidal.left_unitality (E.evenForward ⋙ F.evenForward) X
    change _ ≫ _ ≫ (E.forward.comp F.forward).enriched.forget.map (λ_ X).hom = _
    rw [superfunctor_comp_even_map]
    exact h.symm
  right_unit X := by
    have h := Functor.LaxMonoidal.right_unitality (E.evenForward ⋙ F.evenForward) X
    change _ ≫ _ ≫ (E.forward.comp F.forward).enriched.forget.map (ρ_ X).hom = _
    rw [superfunctor_comp_even_map]
    exact h.symm

def comp : MonoidalSuperequivalence A C := ⟨compData E F, compLaws E F⟩

end MonoidalSuperequivalence
end RMod.Legacy
