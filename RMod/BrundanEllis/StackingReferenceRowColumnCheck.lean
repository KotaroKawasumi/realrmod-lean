import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Pair a stored row with a stored column by traversing both lists once.
This avoids repeated indexing into the matrix inside each scalar product. -/
set_option autoImplicit false
open scoped BigOperators
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor

/-- The ordinary integer scalar product, evaluated on consecutive list entries. -/
def integerListDot (xs ys : List ℤ) : ℤ :=
  (List.zipWith (fun x y => x * y) xs ys).sum

/-- Two lists enumerated by the same index list compute its usual scalar sum. -/
theorem integerListDot_map {J : Type*} (indices : List J) (f g : J → ℤ) :
    integerListDot (indices.map f) (indices.map g) =
      (indices.map fun j => f j * g j).sum := by
  induction indices with
  | nil => rfl
  | cons j js ih =>
    simpa only [integerListDot, List.map_cons, List.zipWith_cons_cons, List.sum_cons]
      using congrArg (fun z => f j * g j + z) ih

/-- Check that an explicit row or column lists the given coordinate function. -/
def tripleVectorCheck {a b c : ℕ}
    (v : Fin a × Fin b × Fin c → ℤ) (entries : List ℤ) : Bool :=
  ((tripleIndices a b c).map v) == entries

theorem tripleVectorCheck_sound {a b c : ℕ}
    (v : Fin a × Fin b × Fin c → ℤ) (entries : List ℤ)
    (h : tripleVectorCheck v entries = true) :
    (tripleIndices a b c).map v = entries :=
  beq_iff_eq.mp h

/-- Matrix multiplication from already verified rows and columns. -/
def rowColumnMul {I K : Type*} (rows : I → List ℤ) (cols : K → List ℤ) : Matrix I K ℤ :=
  fun r s => integerListDot (rows r) (cols s)

theorem rowColumnMul_eq {I K : Type*} {a b c : ℕ}
    (M : Matrix I (Fin a × Fin b × Fin c) ℤ)
    (N : Matrix (Fin a × Fin b × Fin c) K ℤ)
    (rows : I → List ℤ) (cols : K → List ℤ)
    (hrows : ∀ r, (tripleIndices a b c).map (M r) = rows r)
    (hcols : ∀ s, (tripleIndices a b c).map (fun j => N j s) = cols s) :
    rowColumnMul rows cols = M * N := by
  funext r s
  change integerListDot (rows r) (cols s) = ∑ j, M r j * N j s
  rw [← hrows r, ← hcols s, integerListDot_map, sum_tripleIndices]

end RMod.BrundanEllis.Stacking.ReferenceCommutor
