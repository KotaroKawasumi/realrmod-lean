import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Averaging a real three-cocycle on a finite group

Averaging the cocycle equation in its first variable produces an explicit
two-cochain primitive. Right multiplication permutes the group, so no
commutativity of the group is required.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {G : Type*} [Group G] [Fintype G]

/-- The primitive is an actual finite average. -/
noncomputable def averageThreeCochain (f : G → G → G → ℝ) (g h : G) : ℝ :=
  (∑ x, f x g h) / Fintype.card G

theorem averageThreeCochain_coboundary (f : G → G → G → ℝ)
    (hf : ∀ x g h k, f g h k + f x (g * h) k + f x g h =
      f (x * g) h k + f x g (h * k)) (g h k : G) :
    f g h k = averageThreeCochain f h k + averageThreeCochain f g (h * k) -
      averageThreeCochain f (g * h) k - averageThreeCochain f g h := by
  have he := Finset.sum_congr (s₁ := Finset.univ) rfl (fun x _ => hf x g h k)
  have hreindex : (∑ x, f (x * g) h k) = ∑ x, f x h k :=
    Equiv.sum_comp (Equiv.mulRight g) (fun x => f x h k)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    hreindex] at he
  have hn : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  unfold averageThreeCochain
  apply (mul_right_cancel₀ hn)
  simp only [sub_mul, add_mul, div_mul_cancel₀ _ hn]
  linarith

theorem averageThreeCochain_one_left (f : G → G → G → ℝ)
    (hf : ∀ x h, f x 1 h = 0) (h : G) : averageThreeCochain f 1 h = 0 := by
  simp [averageThreeCochain, hf]

theorem averageThreeCochain_one_right (f : G → G → G → ℝ)
    (hf : ∀ x g, f x g 1 = 0) (g : G) : averageThreeCochain f g 1 = 0 := by
  simp [averageThreeCochain, hf]

end RMod.Classification
