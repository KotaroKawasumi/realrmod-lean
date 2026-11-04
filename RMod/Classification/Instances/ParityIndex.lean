import RMod.Classification.Proofs.Parity
import Superfusion.Super.BWTransitivity
import Mathlib.Data.Fintype.EquivFin

/-!
# Sorting a finite parity index

Mathlib's equivalences for complementary subtypes and finite types turn
an arbitrary parity-indexed matrix into the usual p|q block convention.
The ordering choices affect only the resulting matrix coordinates.
-/

set_option autoImplicit false

namespace RMod.Classification

open Superfusion

variable {n : ℕ} (a : Fin n → ZMod 2)

noncomputable def evenCount : ℕ := Fintype.card {i // a i = 0}

noncomputable def oddCount : ℕ := Fintype.card {i // a i ≠ 0}

/-- List the even indices first and the odd indices second. -/
noncomputable def parityIndex : (Fin (evenCount a) ⊕ Fin (oddCount a)) ≃ Fin n :=
  (Equiv.sumCongr (Fintype.equivFin {i // a i = 0}).symm
    (Fintype.equivFin {i // a i ≠ 0}).symm).trans (Equiv.sumCompl (fun i => a i = 0))

theorem parityIndex_grade (i : Fin (evenCount a) ⊕ Fin (oddCount a)) :
    a (parityIndex a i) = sumParity (evenCount a) (oddCount a) i := by
  cases i with
  | inl i =>
    exact ((Fintype.equivFin {i // a i = 0}).symm i).property
  | inr i =>
    exact (parity_cases (a (parityIndex a (Sum.inr i)))).resolve_left
      ((Fintype.equivFin {i // a i ≠ 0}).symm i).property

theorem evenCount_add_oddCount : evenCount a + oddCount a = n := by
  simpa only [Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr (parityIndex a)

/-! These checks retain both parity blocks and do not collapse a nonempty
index set to an empty stabilization. -/

example (a : Fin 2 → ZMod 2) : evenCount a + oddCount a = 2 := evenCount_add_oddCount a

example (a : Fin 8 → ZMod 2) : evenCount a + oddCount a ≠ 0 := by
  rw [evenCount_add_oddCount]
  exact Nat.succ_ne_zero 7

end RMod.Classification
