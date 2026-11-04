import RMod.Classification.Instances.LinearCategory
import RMod.Classification.Abstract.Reference
import Superfusion.Super.TowerClifford

/-!
# Intrinsic endomorphism algebras and Clifford types

Mathlib supplies the endomorphism algebra of the proved linear category.
The raw Clifford predicate in Challenge is equivalent to the usual graded
algebra-isomorphism predicate for this algebra. This bridge lets subsequent
proofs reuse the existing Clifford tower and Brauer--Wall calculations.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (C : WeaklyPointedSuperfusion.{0, 0})

/-- The scalar-unit map is an isomorphism of real algebras, by the split-unit
laws. Its inverse is selected by Mathlib only after bijectivity is proved. -/
noncomputable def unitEndEquiv :
    ℝ ≃ₐ[ℝ] End (C := LinearCategory C) C.data.tensorUnit :=
  AlgEquiv.ofBijective (Algebra.ofId ℝ _) ⟨fun _ _ => C.laws.unit_end_scalar_injective _ _,
    C.laws.unit_end_scalar_surjective⟩

@[simp]
theorem unitEndEquiv_apply (r : ℝ) :
    unitEndEquiv C r = C.data.smul r (C.data.id C.data.tensorUnit) := rfl

/-- End(1) is purely even; this conclusion is derived, not part of P. -/
theorem unit_end_even (f : C.data.Hom C.data.tensorUnit C.data.tensorUnit) :
    C.data.IsHomogeneous 0 f := by
  obtain ⟨r, rfl⟩ := C.laws.unit_end_scalar_surjective f
  exact C.laws.grade_smul r _ (C.laws.id_even _)

theorem unit_end_odd_iff (f : C.data.Hom C.data.tensorUnit C.data.tensorUnit) :
    C.data.IsHomogeneous 1 f ↔ f = C.data.zero := by
  constructor
  · exact C.laws.grade_disjoint f (unit_end_even C f)
  · rintro rfl
    exact C.laws.grade_zero _ _ _

/-- Replace the minimal raw predicate by Mathlib `AlgEquiv`, with the same
grading condition. In particular the order of categorical composition is
checked in the multiplication clause. -/
theorem hasCliffordEnd_iff (X : LinearCategory C) (n : ℕ) :
    HasCliffordEnd C.data X n ↔
      ∃ e : CliffordAlgebra (Superfusion.diagForm (-1 : ℝ) n) ≃ₐ[ℝ] End X,
        ∀ a x, x ∈ CliffordAlgebra.evenOdd (Superfusion.diagForm (-1 : ℝ) n) a ↔
          e x ∈ LinearCategory.grade C X X a := by
  constructor
  · rintro ⟨e, h1, hadd, hsmul, hmul, hgrade⟩
    refine ⟨{ toEquiv := e, map_mul' := hmul, map_add' := hadd, commutes' := ?_ },
      hgrade⟩
    intro r
    rw [Algebra.algebraMap_eq_smul_one]
    change e (r • 1) = C.data.smul r (C.data.id X)
    exact (hsmul r 1).trans (congrArg (C.data.smul r) h1)
  · rintro ⟨e, hgrade⟩
    exact ⟨e.toEquiv, e.map_one, e.map_add,
      fun r x => e.toLinearEquiv.map_smul r x, e.map_mul, hgrade⟩

/-- A Clifford endomorphism algebra has the expected real dimension. The
dimension calculation is the existing tower theorem, not a new assumption. -/
theorem HasCliffordEnd.finrank {X : LinearCategory C} {n : ℕ}
    (h : HasCliffordEnd C.data X n) : Module.finrank ℝ (End X) = 2 ^ n := by
  obtain ⟨e, _⟩ := (hasCliffordEnd_iff C X n).mp h
  rw [← e.toLinearEquiv.finrank_eq]
  exact Superfusion.finrank_cliffordAlgebra_diagForm (-1 : ℝ) n (by norm_num)

/-! The scalar comparison distinguishes actual morphisms, including their
signs; these are nontrivial examples in every split-unit real category. -/

example : unitEndEquiv C (2 : ℝ) ≠ 0 := by
  exact (map_ne_zero_iff (unitEndEquiv C) (unitEndEquiv C).injective).mpr (by norm_num)

example : unitEndEquiv C (-1 : ℝ) ≠ unitEndEquiv C 1 := by
  exact (unitEndEquiv C).injective.ne (by norm_num)

end RMod.Classification
