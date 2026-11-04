import RMod.Classification.Proofs.DecompositionWeights
import RMod.Classification.Proofs.OrbitOrthogonality
import RMod.Classification.Proofs.SimpleTensorEnd

/-!
# Graded centrality forces one homogeneous simple orbit

Assign weight one to one parity orbit of summands and zero to its
complement. Orthogonality makes the diagonal endomorphism central, and it
is even. Graded centrality makes it scalar, forcing all nonzero summands
to have the same weight. Thus a simple decomposition has only one parity
orbit. In particular this holds for tensor products of simple objects.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion Superfusion.Category

variable {C : WeaklyPointedSuperfusion.{0, 0}}

attribute [local implicit_reducible] CategoryTheory.End

theorem Decomposition.sameParityOrbit_of_endSuperCentral {X : LinearCategory C}
    {n : ℕ} {S : Fin n → LinearCategory C} (d : Decomposition C X S)
    (hS : ∀ i, C.data.IsSimple (S i)) [IsSuperCentral (endGrading (K := ℝ) X)]
    (i j : Fin n) : SameParityOrbit C.data (S i) (S j) := by
  classical
  by_contra hij
  let w : Fin n → ℝ := fun k => if SameParityOrbit C.data (S i) (S k) then 1 else 0
  have hw (a b : Fin n) (f : C.data.Hom (S a) (S b)) :
      C.data.smul (w a) f = C.data.smul (w b) f := by
    by_cases hab : SameParityOrbit C.data (S a) (S b)
    · have he : w a = w b := by
        by_cases ha : SameParityOrbit C.data (S i) (S a)
        · have hb := SameParityOrbit.trans C.laws ha hab
          simp only [w, if_pos ha, if_pos hb]
        · have hb : ¬ SameParityOrbit C.data (S i) (S b) :=
            fun hb => ha (SameParityOrbit.trans C.laws hb (SameParityOrbit.symm hab))
          simp only [w, if_neg ha, if_neg hb]
      rw [he]
    · rw [hom_zero_of_not_sameParityOrbit C (hS a) (hS b) hab f, C.laws.smul_zero, C.laws.smul_zero]
  have hc := d.weightedDiagonal_mem_center w hw
  have hsuper : IsSupercentral (endGrading (K := ℝ) X) 0 (d.weightedDiagonal w) := by
    apply (isSupercentral_zero_iff _ _).mpr
    intro a f _
    exact ((Subalgebra.mem_center_iff.mp hc) f).symm
  have hmem : d.weightedDiagonal w ∈ (1 : Submodule ℝ (End X)) :=
    IsSuperCentral.superCenter_le_one
      (le_sup_left (b := superCenterGrade (endGrading (K := ℝ) X) 1)
        ⟨d.weightedDiagonal_even w, hsuper⟩)
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp hmem
  have hi := d.weight_eq_of_scalar w r hr.symm i (simple_id_ne_zero C.laws (hS i))
  have hj := d.weight_eq_of_scalar w r hr.symm j (simple_id_ne_zero C.laws (hS j))
  have he := hi.trans hj.symm
  have hii := SameParityOrbit.refl C.laws (S i)
  simp only [w, if_pos hii, if_neg hij] at he
  exact one_ne_zero he

theorem simple_tensor_isotypic (C : WeaklyPointedSuperfusion.{0, 0})
    (X Y : LinearCategory C) (hX : C.data.IsSimple X) (hY : C.data.IsSimple Y)
    {n : ℕ} {S : Fin n → LinearCategory C}
    (hd : C.data.HasDecomposition (C.data.tensorObj X Y) S)
    (hS : ∀ i, C.data.IsSimple (S i)) (i j : Fin n) :
    SameParityOrbit C.data (S i) (S j) := by
  letI := simple_tensor_end_isSuperCentral C X Y hX hY
  obtain ⟨d⟩ := (hasDecomposition_iff C (C.data.tensorObj X Y) S).mp hd
  exact d.sameParityOrbit_of_endSuperCentral hS i j

end RMod.Classification
