import RMod.BrundanEllis.StackingArithmetic

/-! Universal cochains for powers of a pure degree twist.  The eighth power
has trivial cochains; degrees with even parity have trivial cochains
at every power.  These finite identities will supply cyclic lifts for splitting. -/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 1600000
namespace RMod.BrundanEllis.Stacking

def purePowerNu : ℕ → Multiplicative (ZMod 8) → Multiplicative (ZMod 8) → ZMod 2
  | 0, _, _ => 0
  | n + 1, a, b => purePowerNu n a b + bwBit (a ^ n) * bwBit b

def purePowerSign : ℕ → Multiplicative (ZMod 8) → Multiplicative (ZMod 8) →
    Multiplicative (ZMod 8) → ZMod 2
  | 0, _, _, _ => 0
  | n + 1, a, b, c => purePowerSign n a b c +
      (bwBit ((a * b) ^ n) * bwBit c * purePowerNu n a b +
        bwBit (a ^ n) * bwBit (b * c) * purePowerNu n b c +
        bwPrimitive (a ^ n) * bwBit b * bwBit c +
        bwBit (a ^ n) * (bwBit (b ^ n) * bwBit b) * bwBit c)

theorem purePowerNu_eight (a b : Multiplicative (ZMod 8)) : purePowerNu 8 a b = 0 := by
  fin_cases a <;> fin_cases b <;> rfl

/-- In the revised normalization the eighth power has trivial scalar cochain already. -/
theorem purePowerSign_eight (a b c : Multiplicative (ZMod 8)) :
    purePowerSign 8 a b c = 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl

theorem bwBit_pow (a : Multiplicative (ZMod 8)) (n : ℕ) :
    bwBit (a ^ n) = (n : ZMod 2) * bwBit a := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, bwBit_mul, ih, add_mul]

theorem purePowerNu_even (n : ℕ) (a b : Multiplicative (ZMod 8))
    (hb : bwBit b = 0) : purePowerNu n a b = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [purePowerNu, ih, hb]

theorem purePowerSign_even (n : ℕ) (a b c : Multiplicative (ZMod 8))
    (ha : bwBit a = 0) (hb : bwBit b = 0) (hc : bwBit c = 0) :
    purePowerSign n a b c = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [purePowerSign, ih, ha, hb, hc, bwBit_pow]

/-- Every odd residue modulo eight squares to one. -/
theorem odd_degree_square (a : Multiplicative (ZMod 8)) (ha : bwBit a ≠ 0) :
    a.toAdd * a.toAdd = 1 := by
  fin_cases a <;> first | rfl | exact False.elim (ha rfl)

/-- An odd degree can be killed only by a multiple of eight. -/
theorem eight_dvd_of_odd_pow (a : Multiplicative (ZMod 8)) (n : ℕ)
    (ha : bwBit a ≠ 0) (hn : a ^ n = 1) : 8 ∣ n := by
  have he : (n : ZMod 8) * a.toAdd = 0 := by
    simpa only [toAdd_pow, toAdd_one, nsmul_eq_mul] using congrArg Multiplicative.toAdd hn
  have hz : (n : ZMod 8) = 0 := by
    calc
      (n : ZMod 8) = (n : ZMod 8) * (a.toAdd * a.toAdd) := by rw [odd_degree_square a ha, mul_one]
      _ = ((n : ZMod 8) * a.toAdd) * a.toAdd := (mul_assoc _ _ _).symm
      _ = 0 := by rw [he, zero_mul]
  exact (CharP.cast_eq_zero_iff (ZMod 8) 8 n).mp hz

end RMod.BrundanEllis.Stacking
