import RMod.Classification.Proofs.HomogeneousMatrix
import RMod.Classification.Instances.ParityIndex

/-!
# Homogeneous sums as graded matrix stabilizations

Reindexing the proved endomorphism matrix by its parity gives the exact
matrix stabilization used by the existing Brauer--Wall library. All
isomorphisms below are built from the chosen matrix units and Mathlib
matrix equivalences.
-/

set_option autoImplicit false

namespace RMod.Classification.HomogeneousSum

open CategoryTheory Superfusion

attribute [local implicit_reducible] CategoryTheory.End Matrix
  Category.endSuperAlgebra Category.endGrading SuperAlgebra.matrixSuper

variable {C : WeaklyPointedSuperfusion.{0, 0}}
  {X Y : LinearCategory C} {n : ℕ}
  (d : HomogeneousSum C.data X Y n)

theorem matrixAlgEquiv_map_grade (a : ZMod 2) :
    ((Category.endSuperAlgebra (K := ℝ) Y).grading a).map (matrixAlgEquiv d).toLinearMap =
      matrixGradingA d.data.parity (Category.endSuperAlgebra (K := ℝ) X).grading a := by
  ext m
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact (matrixAlgEquiv_grade_iff d a f).mp hf
  · intro hm
    refine ⟨(matrixAlgEquiv d).symm m, ?_, (matrixAlgEquiv d).apply_symm_apply m⟩
    apply (matrixAlgEquiv_grade_iff d a _).mpr
    simpa only [AlgEquiv.apply_symm_apply] using hm

/-- The graded endomorphism algebra of the sum is the standard p|q matrix
algebra over the graded endomorphism algebra of its homogeneous generator. -/
noncomputable def stabilizationEquivOfIndex {p q : ℕ}
    (e : Fin n ≃ Fin p ⊕ Fin q)
    (he : ∀ i, d.data.parity i = sumParity p q (e i)) :
    SuperAlgEquiv (Category.endSuperAlgebra (K := ℝ) Y)
      ((Category.endSuperAlgebra (K := ℝ) X).matrixSuper p q) where
  toAlgEquiv := (matrixAlgEquiv d).trans
    (Matrix.reindexAlgEquiv ℝ (End X) e)
  map_grading a := by
    rw [show ((matrixAlgEquiv d).trans
        (Matrix.reindexAlgEquiv ℝ (End X) e)).toLinearMap =
      (Matrix.reindexAlgEquiv ℝ (End X) e).toLinearMap.comp
        (matrixAlgEquiv d).toLinearMap from rfl,
      Submodule.map_comp, matrixAlgEquiv_map_grade]
    exact reindexAlgEquiv_map_matrixGradingA _ _ _ e he a

/-- The same comparison, with the parity ordering selected by Mathlib. -/
noncomputable def stabilizationEquiv :
    SuperAlgEquiv (Category.endSuperAlgebra (K := ℝ) Y)
      ((Category.endSuperAlgebra (K := ℝ) X).matrixSuper
        (evenCount d.data.parity) (oddCount d.data.parity)) :=
  stabilizationEquivOfIndex d (parityIndex d.data.parity).symm (fun i => by
    simpa only [Equiv.apply_symm_apply] using
      parityIndex_grade d.data.parity ((parityIndex d.data.parity).symm i))

include d in
/-- Nonempty amplification preserves the Brauer--Wall class. -/
theorem isBWEquivalent (hn : 0 < n) :
    IsBWEquivalent (Category.endSuperAlgebra (K := ℝ) Y)
      (Category.endSuperAlgebra (K := ℝ) X) := by
  exact IsBWEquivalent.of_matrixSuper
    (by rw [evenCount_add_oddCount]; exact Nat.ne_of_gt hn) (stabilizationEquiv d)

end RMod.Classification.HomogeneousSum
