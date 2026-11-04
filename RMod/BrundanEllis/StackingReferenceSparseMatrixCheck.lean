import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Sparse reference rows contain many zero coefficients. Short-circuiting those
summands avoids computing entries of the second matrix that cannot contribute. -/
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor

/-- Evaluate the ordinary product while skipping a summand with zero left factor. -/
def tripleSparseMul {I K : Type*} {a b c : ℕ}
    (M : Matrix I (Fin a × Fin b × Fin c) ℤ)
    (N : Matrix (Fin a × Fin b × Fin c) K ℤ) : Matrix I K ℤ :=
  fun r s => ((tripleIndices a b c).map fun j =>
    let x := M r j
    if x = 0 then 0 else x * N j s).sum

theorem tripleSparseMul_eq {I K : Type*} {a b c : ℕ}
    (M : Matrix I (Fin a × Fin b × Fin c) ℤ)
    (N : Matrix (Fin a × Fin b × Fin c) K ℤ) : tripleSparseMul M N = M * N := by
  rw [← tripleListMul_eq]
  funext r s
  unfold tripleSparseMul tripleListMul
  congr 1
  apply List.map_congr_left
  intro j _
  by_cases h : M r j = 0 <;> simp [h]

end RMod.BrundanEllis.Stacking.ReferenceCommutor
