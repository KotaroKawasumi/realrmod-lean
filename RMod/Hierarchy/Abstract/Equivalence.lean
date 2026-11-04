import RMod.Hierarchy.Abstract.FusionPiSupercategory

/-! Strong monoidal superequivalences preserve the total graded operations. -/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators TensorProduct
namespace RMod.Legacy

structure MonoidalSuperequivalenceData (C D : MonoidalSupercategory) where
  forward : SuperfunctorData C.super.data D.super.data
  backward : SuperfunctorData D.super.data C.super.data
  tensorIso : ∀ X Y : Even C.super,
    evenObj D.super (forward.obj X) ⊗ evenObj D.super (forward.obj Y) ≅
      evenObj D.super (forward.obj (tensorObj (C := Even C.super) X Y))
  unitIso : (𝟙_ (Even D.super)) ≅ evenObj D.super (forward.obj (𝟙_ (Even C.super)))
  unit : ∀ X : Even C.super, X ≅ evenObj C.super (backward.obj (forward.obj X))
  counit : ∀ Y : Even D.super, evenObj D.super (forward.obj (backward.obj Y)) ≅ Y

structure MonoidalSuperequivalenceLaws {C D : MonoidalSupercategory}
    (d : MonoidalSuperequivalenceData C D) : Prop where
  forward : SuperfunctorLaws d.forward
  backward : SuperfunctorLaws d.backward
  unit_natural : ∀ {X Y} (f : THom C.super.data X Y),
    tComp C.super.data f (evenPoint (d.unit Y).hom) =
      tComp C.super.data (evenPoint (d.unit X).hom) (tMap d.backward (tMap d.forward f))
  counit_natural : ∀ {X Y} (f : THom D.super.data X Y),
    tComp D.super.data (tMap d.forward (tMap d.backward f)) (evenPoint (d.counit Y).hom) =
      tComp D.super.data (evenPoint (d.counit X).hom) f
  tensor_natural : ∀ {X X' Y Y'} (f : THom C.super.data X X') (g : THom C.super.data Y Y'),
    tComp D.super.data (tTensor D.data.monoidal (tMap d.forward f) (tMap d.forward g))
      (evenPoint (d.tensorIso X' Y').hom) =
    tComp D.super.data (evenPoint (d.tensorIso X Y).hom)
      (tMap d.forward (tTensor C.data.monoidal f g))
  associativity : ∀ X Y Z : Even C.super,
    ((d.tensorIso X Y).hom ▷ evenObj D.super (d.forward.obj Z)) ≫
      (d.tensorIso (X ⊗ Y) Z).hom ≫
      (Superfunctor.enriched ⟨d.forward, forward⟩).forget.map (α_ X Y Z).hom =
    (α_ (evenObj D.super (d.forward.obj X)) (evenObj D.super (d.forward.obj Y))
      (evenObj D.super (d.forward.obj Z))).hom ≫
      (evenObj D.super (d.forward.obj X) ◁ (d.tensorIso Y Z).hom) ≫
      (d.tensorIso X (Y ⊗ Z)).hom
  left_unit : ∀ X : Even C.super,
    (d.unitIso.hom ▷ evenObj D.super (d.forward.obj X)) ≫ (d.tensorIso (𝟙_ _) X).hom ≫
      (Superfunctor.enriched ⟨d.forward, forward⟩).forget.map (λ_ X).hom =
      (λ_ (evenObj D.super (d.forward.obj X))).hom
  right_unit : ∀ X : Even C.super,
    (evenObj D.super (d.forward.obj X) ◁ d.unitIso.hom) ≫ (d.tensorIso X (𝟙_ _)).hom ≫
      (Superfunctor.enriched ⟨d.forward, forward⟩).forget.map (ρ_ X).hom =
      (ρ_ (evenObj D.super (d.forward.obj X))).hom
structure MonoidalSuperequivalence (C D : MonoidalSupercategory) where
  data : MonoidalSuperequivalenceData C D
  laws : MonoidalSuperequivalenceLaws data

def MonoidallySuperequivalent (C D : MonoidalSupercategory) : Prop :=
  Nonempty (MonoidalSuperequivalence C D)
instance : Coe WeaklyPointedFusionPiSupercategory MonoidalSupercategory :=
  ⟨fun C => C.toMonoidalPiSupercategory.monoidal⟩

end RMod.Legacy
