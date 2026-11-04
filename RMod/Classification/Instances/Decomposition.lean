import RMod.Classification.Abstract.Decomposition
import RMod.Classification.Proofs.Decompositions

/-!
# Coordinates of a chosen decomposition

The original existential predicate supplies exactly these data and laws.
Finite sums of weighted diagonal projections act by the chosen scalar on
each summand. These maps will detect distinct homogeneous simple orbits.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory CategoryTheory.Preadditive

theorem hasDecomposition_iff (C : WeaklyPointedSuperfusion.{u, v})
    (X : C.data.Obj) {n : ℕ} (S : Fin n → C.data.Obj) :
    C.data.HasDecomposition X S ↔ Nonempty (Decomposition C X S) := by
  constructor
  · rintro ⟨i, p, hi, hp, hd, ho, ht⟩
    exact ⟨⟨⟨i, p⟩, ⟨hi, hp, hd, ho, ht⟩⟩⟩
  · rintro ⟨d⟩
    exact ⟨d.data.inclusion, d.data.projection, d.laws.inclusion_even,
      d.laws.projection_even, d.laws.diagonal, d.laws.off_diagonal, d.laws.total⟩

namespace Decomposition

variable {C : WeaklyPointedSuperfusion.{u, v}} {X : LinearCategory C}
  {n : ℕ} {S : Fin n → LinearCategory C} (d : Decomposition C X S)

def weightedDiagonal (w : Fin n → ℝ) : End (C := LinearCategory C) X :=
  ∑ i, w i • (d.data.projection i ≫ d.data.inclusion i : X ⟶ X)

theorem inclusion_weightedDiagonal (w : Fin n → ℝ) (i : Fin n) :
    d.data.inclusion i ≫ d.weightedDiagonal w = C.data.smul (w i) (d.data.inclusion i) := by
  change d.data.inclusion i ≫
    (∑ j, w j • (d.data.projection j ≫ d.data.inclusion j : X ⟶ X)) = _
  rw [comp_sum]
  have he (j : Fin n) :
      d.data.inclusion i ≫ (w j • (d.data.projection j ≫ d.data.inclusion j : X ⟶ X)) =
        if j = i then C.data.smul (w i) (d.data.inclusion i) else C.data.zero := by
    by_cases h : j = i
    · subst j
      rw [if_pos rfl]
      change C.data.comp (d.data.inclusion i)
        (C.data.smul (w i) (C.data.comp (d.data.projection i) (d.data.inclusion i))) = _
      rw [C.laws.comp_smul, ← C.laws.comp_assoc, d.laws.diagonal, C.laws.id_comp]
    · rw [if_neg h]
      change C.data.comp (d.data.inclusion i)
        (C.data.smul (w j) (C.data.comp (d.data.projection j) (d.data.inclusion j))) = _
      rw [C.laws.comp_smul, ← C.laws.comp_assoc, d.laws.off_diagonal i j (Ne.symm h),
        raw_zero_comp C.laws, C.laws.smul_zero]
  simp only [he]
  let v : S i ⟶ X := C.data.smul (w i) (d.data.inclusion i)
  change (∑ k : Fin n, if k = i then v else 0) = v
  simp

theorem weightedDiagonal_projection (w : Fin n → ℝ) (j : Fin n) :
    d.weightedDiagonal w ≫ d.data.projection j = C.data.smul (w j) (d.data.projection j) := by
  change (∑ i, w i • (d.data.projection i ≫ d.data.inclusion i : X ⟶ X)) ≫
    d.data.projection j = _
  rw [sum_comp]
  have he (i : Fin n) :
      (w i • (d.data.projection i ≫ d.data.inclusion i : X ⟶ X)) ≫ d.data.projection j =
        if i = j then C.data.smul (w j) (d.data.projection j) else C.data.zero := by
    by_cases h : i = j
    · subst i
      rw [if_pos rfl]
      change C.data.comp
        (C.data.smul (w j) (C.data.comp (d.data.projection j) (d.data.inclusion j)))
        (d.data.projection j) = _
      rw [C.laws.smul_comp, C.laws.comp_assoc, d.laws.diagonal, C.laws.comp_id]
    · rw [if_neg h]
      change C.data.comp
        (C.data.smul (w i) (C.data.comp (d.data.projection i) (d.data.inclusion i)))
        (d.data.projection j) = _
      rw [C.laws.smul_comp, C.laws.comp_assoc, d.laws.off_diagonal i j h,
        raw_comp_zero C.laws, C.laws.smul_zero]
  simp only [he]
  let v : X ⟶ S j := C.data.smul (w j) (d.data.projection j)
  change (∑ i : Fin n, if i = j then v else 0) = v
  simp

end Decomposition

end RMod.Classification
