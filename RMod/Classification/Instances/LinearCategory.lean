import RMod.Definitions.WeaklyPointedSuperfusion
import RMod.Classification.Proofs.Parity
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.BigOperators.Fin

/-!
# Mathlib instances for the intrinsic Hom operations

The immutable statement stores operations and laws separately. This module
uses the laws of a completed category to install Mathlib's category, additive
group and real module instances, without choosing new Hom operations. In
particular Mathlib supplies the endomorphism ring and algebra, with product
`f * g = g ≫ f`. The object synonym confines these instances to this adapter.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

/-- The same objects, viewed through the proved Mathlib category instances. -/
@[implicit_reducible]
def LinearCategory (C : WeaklyPointedSuperfusion.{u, v}) : Type u := C.data.Obj

namespace LinearCategory

open CategoryTheory

variable (C : WeaklyPointedSuperfusion.{u, v})

instance category : Category.{v} (LinearCategory C) where
  Hom X Y := C.data.Hom X Y
  id X := C.data.id X
  comp f g := C.data.comp f g
  id_comp := C.laws.id_comp
  comp_id := C.laws.comp_id
  assoc := C.laws.comp_assoc

instance preadditive : Preadditive (LinearCategory C) where
  homGroup X Y := by
    letI : Zero (X ⟶ Y) := ⟨C.data.zero⟩
    letI : Add (X ⟶ Y) := ⟨C.data.add⟩
    letI : Neg (X ⟶ Y) := ⟨C.data.neg⟩
    exact
    { add := C.data.add
      zero := C.data.zero
      neg := C.data.neg
      nsmul := nsmulRec
      zsmul := zsmulRec
      add_assoc := C.laws.add_assoc
      zero_add := C.laws.zero_add
      add_zero := C.laws.add_zero
      neg_add_cancel := C.laws.neg_add
      add_comm := C.laws.add_comm }
  add_comp _ _ _ := C.laws.add_comp
  comp_add _ _ _ := C.laws.comp_add

instance linear : Linear ℝ (LinearCategory C) where
  homModule _ _ :=
    { smul := C.data.smul
      one_smul := C.laws.one_smul
      mul_smul := C.laws.mul_smul
      smul_add := C.laws.smul_add
      smul_zero := C.laws.smul_zero
      add_smul := C.laws.add_smul
      zero_smul := C.laws.zero_smul }
  smul_comp _ _ _ := C.laws.smul_comp
  comp_smul _ _ _ f r g := C.laws.comp_smul r f g

/-! The statement's ordered sums agree with Mathlib's finite sums. -/

theorem finSum_eq_sum {X Y : LinearCategory C} (n : ℕ) (f : Fin n → (X ⟶ Y)) :
    C.data.finSum n f = ∑ i, f i := by
  induction n with
  | zero => simp [WeaklyPointedSuperfusionData.finSum]; rfl
  | succ n ih =>
    rw [WeaklyPointedSuperfusionData.finSum, Fin.sum_univ_castSucc, ih]
    rfl

/-! Homogeneous components are actual submodules, and their sum is internal. -/

def grade (X Y : LinearCategory C) (a : ZMod 2) : Submodule ℝ (X ⟶ Y) where
  carrier := C.data.grade X Y a
  zero_mem' := C.laws.grade_zero X Y a
  add_mem' := C.laws.grade_add _ _
  smul_mem' r _ hf := C.laws.grade_smul r _ hf

@[simp]
theorem mem_grade {X Y : LinearCategory C} {a : ZMod 2} (f : X ⟶ Y) :
    f ∈ grade C X Y a ↔ C.data.IsHomogeneous a f := Iff.rfl

theorem grade_isCompl (X Y : LinearCategory C) :
    IsCompl (grade C X Y 0) (grade C X Y 1) := by
  constructor
  · exact Submodule.disjoint_def.mpr (fun f hf hg => C.laws.grade_disjoint f hf hg)
  · exact Submodule.codisjoint_iff_exists_add_eq.mpr C.laws.grade_decomposition

theorem grade_isInternal (X Y : LinearCategory C) :
    DirectSum.IsInternal (grade C X Y) := by
  have h : (Set.univ : Set (ZMod 2)) = {0, 1} := by
    ext a
    simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]
    exact parity_cases a
  exact (DirectSum.isInternal_submodule_iff_isCompl _ zero_ne_one h).mpr
    (grade_isCompl C X Y)

/-! Finite spanning families from the laws give Mathlib finite dimensionality.
No basis or coordinate function is chosen by this proof-only adapter. -/

instance finiteDimensionalHom (X Y : LinearCategory C) : FiniteDimensional ℝ (X ⟶ Y) := by
  obtain ⟨n, b, c, hspan, _⟩ := C.laws.finite_dimensional_hom X Y
  let basis : Fin n → (X ⟶ Y) := b
  have htop : Submodule.span ℝ (Set.range basis) = (⊤ : Submodule ℝ (X ⟶ Y)) := by
    apply top_unique
    intro f _
    rw [← hspan f, finSum_eq_sum C]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact Module.Finite.of_fg_top
    (Submodule.fg_iff_exists_fin_generating_family.mpr ⟨n, basis, htop⟩)

end LinearCategory
end RMod.Classification
