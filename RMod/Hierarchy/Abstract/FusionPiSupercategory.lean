import RMod.Hierarchy.Instances.EvenMonoidal

/-! Fusion, rigidity, split unit, and weak invertibility are properties of the specified data. -/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators TensorProduct
namespace RMod.Legacy

def IsRigid (C : MonoidalSupercategory) : Prop := Nonempty (RigidCategory (Even C.super))
def IsSplitUnit (C : MonoidalSupercategory) : Prop :=
  Nonempty (CategoryTheory.End (totalObj C.super C.data.monoidal.unit) ≃ₐ[ℝ] ℝ)

/-! Fusion and weak pointedness add only propositions to completed structures. -/
structure FusionPiSupercategory extends MonoidalPiSupercategory where
  rigid : IsRigid toMonoidalPiSupercategory.monoidal
  biproducts : HasFiniteBiproducts (Even toMonoidalPiSupercategory.monoidal.super)
  hom_finite : ∀ X Y a, FiniteDimensional ℝ (data.Hom X Y a)
  semisimple : letI := biproducts
    ∀ X : Even toMonoidalPiSupercategory.monoidal.super,
      ∃ (n : ℕ) (S : Fin n → Even toMonoidalPiSupercategory.monoidal.super),
        (∀ i, Simple (S i)) ∧ Nonempty (X ≅ ⨁ S)
  finite_simples : ∃ (n : ℕ) (S : Fin n → Even toMonoidalPiSupercategory.monoidal.super),
    (∀ i, Simple (S i)) ∧ ∀ X : Even toMonoidalPiSupercategory.monoidal.super, Simple X →
      ∃ i, SameParityOrbit toMonoidalPiSupercategory.monoidal.super X (S i)
  graded_schur : ∀ (X Y : Even toMonoidalPiSupercategory.monoidal.super),
    Simple X → Simple Y → ∀ a (f : THom data.toSupercategoryData X Y),
      f ∈ grade toMonoidalPiSupercategory.monoidal.super X Y a → f ≠ 0 →
        @IsIso (TotalCategory toMonoidalPiSupercategory.monoidal.super) _ X Y f
  simple_unit : Simple (evenObj toMonoidalPiSupercategory.monoidal.super data.monoidal.unit)

instance (C : FusionPiSupercategory) :
    HasFiniteBiproducts (Even C.toMonoidalPiSupercategory.monoidal.super) := C.biproducts

/-- In `ExactPairing X Y`, Y is a Mathlib right dual (an EGNO left dual). -/
def IsWeaklyInvertible (C : MonoidalPiSupercategory)
    [HasFiniteBiproducts (Even C.monoidal.super)] (X : Even C.monoidal.super) : Prop :=
  ∃ Y : Even C.monoidal.super, Nonempty (ExactPairing X Y) ∧
    ∃ p q : ℕ, Nonempty (X ⊗ Y ≅ ⨁ (fun i : Fin p ⊕ Fin q =>
      Sum.elim (fun _ => (𝟙_ (Even C.monoidal.super)))
        (fun _ => evenObj C.monoidal.super (C.data.parityShift.functor.obj C.data.monoidal.unit)) i))
def IsWeaklyPointed (C : FusionPiSupercategory) : Prop :=
  ∀ X : Even C.toMonoidalPiSupercategory.monoidal.super,
    Simple X → IsWeaklyInvertible C.toMonoidalPiSupercategory X
structure WeaklyPointedFusionPiSupercategory extends FusionPiSupercategory where
  splitUnit : IsSplitUnit toMonoidalPiSupercategory.monoidal
  weaklyPointed : IsWeaklyPointed toFusionPiSupercategory

end RMod.Legacy
