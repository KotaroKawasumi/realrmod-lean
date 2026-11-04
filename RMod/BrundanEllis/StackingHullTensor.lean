import RMod.BrundanEllis.StackingHullSums
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-! Closure of the completion can be checked on the original and parity-shifted
generators. Rigidity supplies the additive tensor functors used to extend the
calculation through finite sums and even retracts. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.AddPiHull

variable {C D : WeaklyPointedFusionPiSuperCat} {I J : Type}
  {Z : I → Even C} {W : J → Even D}

/-- An additive functor maps the whole hull into a hull once it does so on the
original and parity-shifted generators. -/
theorem map (F : Even C ⥤ Even D) [F.Additive]
    (h : ∀ i (p : Bool), AddPiHull D W (F.obj
      (if p then evenObj C (MonoidalPiSuperCategory.pi (C := C)) ⊗ Z i else Z i)))
    {X : Even C} (hX : AddPiHull C Z X) : AddPiHull D W (F.obj X) := by
  obtain ⟨n, i, p, ⟨r⟩⟩ := hX
  let family := fun j : Fin n =>
    if p j then evenObj C (MonoidalPiSuperCategory.pi (C := C)) ⊗ Z (i j) else Z (i j)
  exact of_retract ((r.map F).trans (Retract.ofIso (F.mapBiproduct family)))
    (finite_biproduct (F.obj ∘ family) (fun j => h (i j) (p j)))

/-- A rigid left tensor functor is a right adjoint, hence preserves finite products. -/
theorem leftTensorAdditive (X : Even C) : (tensorLeft X).Additive := by
  letI := (tensorLeftAdjunction X (Xᘁ)).isRightAdjoint
  exact Functor.additive_of_preserves_binary_products (tensorLeft X)

/-- The other dual supplies the analogous result for right tensor. -/
theorem rightTensorAdditive (X : Even C) : (tensorRight X).Additive := by
  letI := (tensorRightAdjunction (ᘁX) X).isRightAdjoint
  exact Functor.additive_of_preserves_binary_products (tensorRight X)

/-- Tensor closure reduces to the four parity choices for pairs of generators. -/
theorem tensor_of_generators
    (h : ∀ i j (p q : Bool), AddPiHull C Z
      ((if p then evenObj C (MonoidalPiSuperCategory.pi (C := C)) ⊗ Z i else Z i) ⊗
       (if q then evenObj C (MonoidalPiSuperCategory.pi (C := C)) ⊗ Z j else Z j)))
    {X Y : Even C} (hX : AddPiHull C Z X) (hY : AddPiHull C Z Y) :
    AddPiHull C Z (X ⊗ Y) := by
  letI := rightTensorAdditive Y
  apply map (tensorRight Y) (fun i p => ?_) hX
  let A := if p then evenObj C (MonoidalPiSuperCategory.pi (C := C)) ⊗ Z i else Z i
  letI := leftTensorAdditive A
  exact map (tensorLeft A) (fun j q => h i j p q) hY

end RMod.BrundanEllis.AddPiHull
