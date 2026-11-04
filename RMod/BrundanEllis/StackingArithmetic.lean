import RMod.BrundanEllis.StackingSurface
import Superfusion.Cochain.Cup

/-! Arithmetic identities for the fixed sign, parity, primitive and carry cochains. -/
noncomputable section
set_option autoImplicit false
namespace RMod.BrundanEllis
namespace Stacking

@[simp] theorem realSign_zero : realSign 0 = 1 := by simp [realSign]
theorem realSign_add (a b : ZMod 2) : realSign (a + b) = realSign a * realSign b :=
  RMod.Classification.realSign_add a b
@[simp] theorem realSign_sq (a : ZMod 2) : realSign a * realSign a = 1 := by
  rw [← realSign_add, CharTwo.add_self_eq_zero, realSign_zero]
@[simp] theorem bwBit_one : bwBit 1 = 0 := rfl
@[simp] theorem bwCarry_one_left (a : Multiplicative (ZMod 8)) : bwCarry 1 a = 0 := by
  simp [bwCarry, show a.toAdd.val < 8 from (ZMod.val_lt _)]
@[simp] theorem bwCarry_one_right (a : Multiplicative (ZMod 8)) : bwCarry a 1 = 0 := by
  simp [bwCarry, show a.toAdd.val < 8 from (ZMod.val_lt _)]
@[simp] theorem bwPrimitive_one : bwPrimitive 1 = 0 := rfl

theorem bwBit_mul (a b : Multiplicative (ZMod 8)) :
    bwBit (a * b) = bwBit a + bwBit b := by
  change (ZMod.castHom (by norm_num : 2 ∣ 8) (ZMod 2)) (a.toAdd + b.toAdd) = _
  exact map_add _ _ _

theorem bwPrimitive_mul (a b : Multiplicative (ZMod 8)) :
    bwPrimitive (a * b) = bwPrimitive a + bwPrimitive b + bwBit a * bwBit b := by
  fin_cases a <;> fin_cases b <;> rfl

/-- The carry is the binary cocycle for the extension from mod 8 to mod 16. -/
theorem bwCarry_cocycle (a b c : Multiplicative (ZMod 8)) :
    bwCarry b c + bwCarry (a * b) c + bwCarry a (b * c) + bwCarry a b = 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl

end Stacking
end RMod.BrundanEllis
