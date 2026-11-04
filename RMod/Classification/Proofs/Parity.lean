import RMod.Classification.Abstract.Pi
import Mathlib.Algebra.CharP.Two

/-! Elementary parity lemmas used only by the proofs. -/

set_option autoImplicit false

namespace RMod.Classification

/-- Two-case elimination in the parity group, with no project dependency. -/
theorem parity_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  refine Fin.cases (Or.inl rfl) (fun b => ?_) a
  exact Fin.cases (Or.inr rfl) (fun c => Fin.elim0 c) b

end RMod.Classification
