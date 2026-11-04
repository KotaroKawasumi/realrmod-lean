import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! Coherence of the corrected exterior tensor comparison and normalization of its unit. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace RMod.BrundanEllis.Stacking
open CategoryTheory CategoryTheory.MonoidalCategory
universe vD uD
variable {D : Type uD} [Category.{vD} D] [MonoidalCategory D]

/-- Tensoring with an object isomorphic to the unit is fully faithful.
The inverse on maps is retained by the existing mathlib structure. -/
def tensorRightUnitFullyFaithful {M : D} (e : M ≅ 𝟙_ D) :
    (tensorRight M).FullyFaithful :=
  (Functor.FullyFaithful.ofFullyFaithful (𝟭 D)).ofIso
    (((curriedTensor D).flip.mapIso e) ≪≫ rightUnitorNatIso D).symm

/-- Normalize an invertible multiplication on a unit object by cancelling
its right tensor factor. This selects the actual unit isomorphism. -/
def multiplicationUnitIso {M : D} (e : M ≅ 𝟙_ D) (m : M ⊗ M ≅ M) : 𝟙_ D ≅ M :=
  (tensorRightUnitFullyFaithful e).preimageIso ((λ_ M) ≪≫ m.symm)

/-- The normalized unit satisfies the left unit identity on M itself. -/
theorem multiplicationUnitIso_left {M : D} (e : M ≅ 𝟙_ D) (m : M ⊗ M ≅ M) :
    (multiplicationUnitIso e m).hom ▷ M ≫ m.hom = (λ_ M).hom := by
  have hm := (tensorRightUnitFullyFaithful e).map_preimage (((λ_ M) ≪≫ m.symm).hom)
  change (multiplicationUnitIso e m).hom ▷ M = (λ_ M).hom ≫ m.inv at hm
  rw [hm, Category.assoc, m.inv_hom_id, Category.comp_id]

/-- An invertible associative left action inherits the normalized unit
identity, by cancellation of the action map. -/
theorem invertibleLeftAction_unit {M A : D}
    (m : M ⊗ M ≅ M) (l : M ⊗ A ≅ A) (ε : 𝟙_ D ≅ M)
    (hm : ε.hom ▷ M ≫ m.hom = (λ_ M).hom)
    (ha : m.hom ▷ A ≫ l.hom = (α_ M M A).hom ≫ M ◁ l.hom ≫ l.hom) :
    ε.hom ▷ A ≫ l.hom = (λ_ A).hom := by
  apply (cancel_epi ((α_ (𝟙_ D) M A).hom ≫ (𝟙_ D) ◁ l.hom)).1
  simp only [Category.assoc]
  calc
    (α_ (𝟙_ D) M A).hom ≫ (𝟙_ D) ◁ l.hom ≫ ε.hom ▷ A ≫ l.hom =
        (α_ (𝟙_ D) M A).hom ≫ ε.hom ▷ (M ⊗ A) ≫ M ◁ l.hom ≫ l.hom := by
      rw [whisker_exchange_assoc]
    _ = (ε.hom ▷ M) ▷ A ≫ (α_ M M A).hom ≫ M ◁ l.hom ≫ l.hom := by
      rw [associator_naturality_left_assoc]
    _ = (ε.hom ▷ M) ▷ A ≫ m.hom ▷ A ≫ l.hom := by rw [ha]
    _ = (λ_ M).hom ▷ A ≫ l.hom := by rw [← comp_whiskerRight_assoc, hm]
    _ = (α_ (𝟙_ D) M A).hom ≫ (𝟙_ D) ◁ l.hom ≫ (λ_ A).hom := by
      rw [leftUnitor_naturality, leftUnitor_tensor_hom, Category.assoc, Iso.hom_inv_id_assoc]

/-- The right action unit identity follows from the same normalization,
the action associativity equation and faithful right tensoring with M. -/
theorem invertibleRightAction_unit {M A : D} (e : M ≅ 𝟙_ D)
    (m : M ⊗ M ≅ M) (r : A ⊗ M ≅ A) (ε : 𝟙_ D ≅ M)
    (hm : ε.hom ▷ M ≫ m.hom = (λ_ M).hom)
    (ha : r.hom ▷ M ≫ r.hom = (α_ A M M).hom ≫ A ◁ m.hom ≫ r.hom) :
    A ◁ ε.hom ≫ r.hom = (ρ_ A).hom := by
  apply (tensorRightUnitFullyFaithful e).map_injective
  change (A ◁ ε.hom ≫ r.hom) ▷ M = (ρ_ A).hom ▷ M
  apply (cancel_mono r.hom).1
  rw [comp_whiskerRight, Category.assoc, ha, associator_naturality_middle_assoc,
    ← whiskerLeft_comp_assoc, hm, triangle_assoc]

end RMod.BrundanEllis.Stacking

namespace RMod.BrundanEllis.Stacking
open CategoryTheory CategoryTheory.MonoidalCategory
universe vC vD uC uD
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
  (F : C ⥤ D) (μ : ∀ X Y, F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y))

/-- The unit image carries an invertible multiplication induced by the
binary comparison and the original unit constraint. -/
def semigroupalMultiplicationIso : F.obj (𝟙_ C) ⊗ F.obj (𝟙_ C) ≅ F.obj (𝟙_ C) :=
  μ (𝟙_ C) (𝟙_ C) ≪≫ F.mapIso (λ_ (𝟙_ C))

/-- The unit image acts on each image object on the left. -/
def semigroupalLeftActionIso (X : C) : F.obj (𝟙_ C) ⊗ F.obj X ≅ F.obj X :=
  μ (𝟙_ C) X ≪≫ F.mapIso (λ_ X)

/-- The corresponding invertible right action. -/
def semigroupalRightActionIso (X : C) : F.obj X ⊗ F.obj (𝟙_ C) ≅ F.obj X :=
  μ X (𝟙_ C) ≪≫ F.mapIso (ρ_ X)

variable
  (hnL : ∀ {X Y : C} (f : X ⟶ Y) (Z : C),
    F.map f ▷ F.obj Z ≫ (μ Y Z).hom = (μ X Z).hom ≫ F.map (f ▷ Z))
  (hnR : ∀ {X Y : C} (Z : C) (f : X ⟶ Y),
    F.obj Z ◁ F.map f ≫ (μ Z Y).hom = (μ Z X).hom ≫ F.map (Z ◁ f))
  (ha : ∀ X Y Z : C,
    (μ X Y).hom ▷ F.obj Z ≫ (μ (X ⊗ Y) Z).hom ≫ F.map (α_ X Y Z).hom =
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ F.obj X ◁ (μ Y Z).hom ≫ (μ X (Y ⊗ Z)).hom)

include hnL hnR ha

/-- Functorial naturality and the binary associativity equation imply
associativity of the induced left action. -/
theorem semigroupalLeftAction_associative (X : C) :
    (semigroupalMultiplicationIso F μ).hom ▷ F.obj X ≫ (semigroupalLeftActionIso F μ X).hom =
      (α_ (F.obj (𝟙_ C)) (F.obj (𝟙_ C)) (F.obj X)).hom ≫
        F.obj (𝟙_ C) ◁ (semigroupalLeftActionIso F μ X).hom ≫
        (semigroupalLeftActionIso F μ X).hom := by
  have hc : (λ_ (𝟙_ C)).hom ▷ X ≫ (λ_ X).hom =
      (α_ (𝟙_ C) (𝟙_ C) X).hom ≫ (𝟙_ C) ◁ (λ_ X).hom ≫ (λ_ X).hom := by
    rw [leftUnitor_naturality, leftUnitor_tensor_hom, Category.assoc, Iso.hom_inv_id_assoc]
  dsimp only [semigroupalMultiplicationIso, semigroupalLeftActionIso, Iso.trans, Functor.mapIso]
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% (hnL (λ_ (𝟙_ C)).hom X), ← F.map_comp, hc,
    F.map_comp, F.map_comp, reassoc_of% (ha (𝟙_ C) (𝟙_ C) X),
    ← reassoc_of% (hnR (𝟙_ C) (λ_ X).hom)]

/-- The same equations make the induced right action associative. -/
theorem semigroupalRightAction_associative (X : C) :
    (semigroupalRightActionIso F μ X).hom ▷ F.obj (𝟙_ C) ≫ (semigroupalRightActionIso F μ X).hom =
      (α_ (F.obj X) (F.obj (𝟙_ C)) (F.obj (𝟙_ C))).hom ≫
        F.obj X ◁ (semigroupalMultiplicationIso F μ).hom ≫
        (semigroupalRightActionIso F μ X).hom := by
  have hc : (ρ_ X).hom ▷ (𝟙_ C) ≫ (ρ_ X).hom =
      (α_ X (𝟙_ C) (𝟙_ C)).hom ≫ X ◁ (λ_ (𝟙_ C)).hom ≫ (ρ_ X).hom := by
    rw [triangle_assoc]
  dsimp only [semigroupalMultiplicationIso, semigroupalRightActionIso, Iso.trans, Functor.mapIso]
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% (hnL (ρ_ X).hom (𝟙_ C)), ← F.map_comp, hc,
    F.map_comp, F.map_comp, reassoc_of% (ha X (𝟙_ C) (𝟙_ C)),
    ← reassoc_of% (hnR X (λ_ (𝟙_ C)).hom)]

end RMod.BrundanEllis.Stacking

namespace RMod.BrundanEllis.Stacking
open CategoryTheory CategoryTheory.MonoidalCategory
universe vC vD uC uD
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
  (F : C ⥤ D) (μ : ∀ X Y, F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y))
  (e : F.obj (𝟙_ C) ≅ 𝟙_ D)

/-- A specified unit comparison determined by the binary data and any
initial isomorphism between the unit image and the target unit. -/
def semigroupalUnitIso : 𝟙_ D ≅ F.obj (𝟙_ C) :=
  multiplicationUnitIso e (semigroupalMultiplicationIso F μ)

variable
  (hnL : ∀ {X Y : C} (f : X ⟶ Y) (Z : C),
    F.map f ▷ F.obj Z ≫ (μ Y Z).hom = (μ X Z).hom ≫ F.map (f ▷ Z))
  (hnR : ∀ {X Y : C} (Z : C) (f : X ⟶ Y),
    F.obj Z ◁ F.map f ≫ (μ Z Y).hom = (μ Z X).hom ≫ F.map (Z ◁ f))
  (ha : ∀ X Y Z : C,
    (μ X Y).hom ▷ F.obj Z ≫ (μ (X ⊗ Y) Z).hom ≫ F.map (α_ X Y Z).hom =
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ F.obj X ◁ (μ Y Z).hom ≫ (μ X (Y ⊗ Z)).hom)

/-- Associative, invertible, natural binary comparisons become a strong
monoidal functor whenever the unit image is isomorphic to the unit.
Both unit laws are proved by cancellation; they are not extra assumptions. -/
def coreMonoidalOfAssociativity : F.CoreMonoidal where
  εIso := semigroupalUnitIso F μ e
  μIso := μ
  μIso_hom_natural_left := hnL
  μIso_hom_natural_right := hnR
  associativity := ha
  left_unitality X := by
    exact (invertibleLeftAction_unit (semigroupalMultiplicationIso F μ)
      (semigroupalLeftActionIso F μ X) (semigroupalUnitIso F μ e)
      (multiplicationUnitIso_left e (semigroupalMultiplicationIso F μ))
      (semigroupalLeftAction_associative F μ hnL hnR ha X)).symm
  right_unitality X := by
    exact (invertibleRightAction_unit e (semigroupalMultiplicationIso F μ)
      (semigroupalRightActionIso F μ X) (semigroupalUnitIso F μ e)
      (multiplicationUnitIso_left e (semigroupalMultiplicationIso F μ))
      (semigroupalRightAction_associative F μ hnL hnR ha X)).symm

end RMod.BrundanEllis.Stacking
