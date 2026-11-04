import Mathlib.Data.Matrix.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Fin

/-! List-based verification avoids constructing a dependent matrix decider.
Soundness uses only List.all_eq_true and matrix extensionality. -/
set_option autoImplicit false
open scoped BigOperators
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor

/-- Compare the entries at two explicit finite lists of indices. -/
def matrixEntryCheck {I J : Type*} (rows : List I) (cols : List J)
    (M N : Matrix I J ℤ) : Bool :=
  rows.all fun r => cols.all fun s => M r s == N r s

/-- A successful comparison over exhaustive lists proves matrix equality. -/
theorem matrixEntryCheck_sound {I J : Type*} (rows : List I) (cols : List J)
    (hrows : ∀ r, r ∈ rows) (hcols : ∀ s, s ∈ cols) (M N : Matrix I J ℤ)
    (h : matrixEntryCheck rows cols M N = true) : M = N := by
  apply Matrix.ext
  intro r s
  have hr := List.all_eq_true.mp h r (hrows r)
  exact beq_iff_eq.mp (List.all_eq_true.mp hr s (hcols s))

/-- Enumerate the ordinary three-component index used by the reference maps. -/
def tripleIndices (a b c : ℕ) : List (Fin a × Fin b × Fin c) :=
  (List.finRange a).flatMap fun r => (List.finRange b).flatMap fun s =>
    (List.finRange c).map fun t => (r, s, t)

theorem mem_tripleIndices (a b c : ℕ) (x : Fin a × Fin b × Fin c) :
    x ∈ tripleIndices a b c := by
  rcases x with ⟨r, s, t⟩
  simp [tripleIndices]

/-- Checking one row at a time bounds the kernel's temporary reduction state. -/
def tripleRowCheck {a b c : ℕ}
    (v w : Fin a × Fin b × Fin c → ℤ) : Bool :=
  (tripleIndices a b c).all fun s => v s == w s

theorem tripleRowCheck_sound {a b c : ℕ}
    (v w : Fin a × Fin b × Fin c → ℤ)
    (h : tripleRowCheck v w = true) : v = w := by
  funext s
  exact beq_iff_eq.mp (List.all_eq_true.mp h s (mem_tripleIndices a b c s))

/-- Every reference matrix equality can be certified by one List program. -/
theorem tripleMatrixCheck_sound {a b c d e f : ℕ}
    (M N : Matrix (Fin a × Fin b × Fin c) (Fin d × Fin e × Fin f) ℤ)
    (h : matrixEntryCheck (tripleIndices a b c) (tripleIndices d e f) M N = true) : M = N :=
  matrixEntryCheck_sound _ _ (mem_tripleIndices a b c) (mem_tripleIndices d e f) M N h


/-- Split a list sum into its consecutive finite blocks. -/
theorem sum_map_flatMap {I J : Type*} (xs : List I) (ys : I → List J) (f : J → ℤ) :
    ((xs.flatMap ys).map f).sum = (xs.map fun i => ((ys i).map f).sum).sum := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp [ih]

/-- List summation agrees with the usual sum on the triple product. -/
theorem sum_tripleIndices (a b c : ℕ) (f : Fin a × Fin b × Fin c → ℤ) :
    ((tripleIndices a b c).map f).sum = ∑ i, f i := by
  simp only [tripleIndices, sum_map_flatMap, List.map_map, Function.comp_def,
    Fintype.sum_prod_type, Fin.sum_univ_def]

/-- The same matrix product evaluated by a plain List program. -/
def tripleListMul {I K : Type*} {a b c : ℕ}
    (M : Matrix I (Fin a × Fin b × Fin c) ℤ)
    (N : Matrix (Fin a × Fin b × Fin c) K ℤ) : Matrix I K ℤ :=
  fun r s => ((tripleIndices a b c).map fun j => M r j * N j s).sum

theorem tripleListMul_eq {I K : Type*} {a b c : ℕ}
    (M : Matrix I (Fin a × Fin b × Fin c) ℤ)
    (N : Matrix (Fin a × Fin b × Fin c) K ℤ) : tripleListMul M N = M * N := by
  funext r s
  exact sum_tripleIndices a b c (fun j => M r j * N j s)

end RMod.BrundanEllis.Stacking.ReferenceCommutor
