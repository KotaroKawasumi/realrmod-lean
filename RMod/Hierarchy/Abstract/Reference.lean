import RMod.Hierarchy.Abstract.Equivalence

/-! Brauer–Wall reference types use graded endomorphism algebras of finite sums. -/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators TensorProduct
namespace RMod.Legacy

def HasBrauerWallType (C : FusionPiSupercategory)
    (X : Even C.toMonoidalPiSupercategory.monoidal.super) (r : ZMod 8) : Prop :=
  let A := C.toMonoidalPiSupercategory.monoidal.super
  letI : HasFiniteBiproducts (Even A) := C.biproducts
  let Q := QuadraticMap.weightedSumSquares ℝ (fun _ : Fin r.val => (-1 : ℝ))
  ∃ (n : ℕ) (S : Fin n → Even A), 0 < n ∧
    (∀ i, SameParityOrbit A X (S i)) ∧
    ∃ e : CliffordAlgebra Q ≃ₐ[ℝ] CategoryTheory.End (totalObj A (biproduct (C := Even A) S)),
      ∀ a x, x ∈ CliffordAlgebra.evenOdd Q a ↔ e x ∈ grade A (biproduct (C := Even A) S) (biproduct (C := Even A) S) a
structure IsBrauerWallReference (C : WeaklyPointedFusionPiSupercategory) : Prop where
  simple_type : ∀ X : Even C.toMonoidalPiSupercategory.monoidal.super,
    Simple X → ∃! r, HasBrauerWallType C.toFusionPiSupercategory X r
  realizes_type : ∀ r, ∃ X : Even C.toMonoidalPiSupercategory.monoidal.super,
    Simple X ∧ HasBrauerWallType C.toFusionPiSupercategory X r
  type_detects_orbit : ∀ (X Y : Even C.toMonoidalPiSupercategory.monoidal.super) r,
    Simple X → Simple Y → HasBrauerWallType C.toFusionPiSupercategory X r →
    (HasBrauerWallType C.toFusionPiSupercategory Y r ↔
      SameParityOrbit C.toMonoidalPiSupercategory.monoidal.super X Y)

end RMod.Legacy
