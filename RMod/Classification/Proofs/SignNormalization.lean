import RMod.Classification.Instances.SignNormalizationData

/-!
# Removal of positive real scalars

The logarithm of the signed pentagon is an ordinary real cocycle because
the logarithm of either sign is zero. Finite averaging gives its primitive.
Exponentiating that primitive supplies the normalized gauge with lambda
zero, and applying the sign homomorphism proves the target pentagon.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {t : TwistData} (ht : TwistLaws t)

include ht

theorem twistLog_cocycle (x g h k : t.group) :
    twistLog t g h k + twistLog t x (g * h) k + twistLog t x g h =
      twistLog t (x * g) h k + twistLog t x g (h * k) := by
  have he := congrArg unitLog (ht.pentagon x g h k)
  simp only [map_mul, unitLog_realSign, one_mul] at he
  exact he

theorem twistLog_one_middle (x h : t.group) : twistLog t x 1 h = 0 := by
  unfold twistLog
  rw [ht.omega_one₂, map_one]
  rfl

theorem twistLog_one_right (x g : t.group) : twistLog t x g 1 = 0 := by
  unfold twistLog
  rw [ht.omega_one₃, map_one]
  rfl

theorem twistLogPrimitive_one_left (h : t.group) : twistLogPrimitive t 1 h = 0 := by
  letI := Fintype.ofFinite t.group
  exact averageThreeCochain_one_left (twistLog t) (twistLog_one_middle ht) h

theorem twistLogPrimitive_one_right (g : t.group) : twistLogPrimitive t g 1 = 0 := by
  letI := Fintype.ofFinite t.group
  exact averageThreeCochain_one_right (twistLog t) (twistLog_one_right ht) g

theorem twistLogPrimitive_coboundary (g h k : t.group) :
    twistLog t g h k = twistLogPrimitive t h k + twistLogPrimitive t g (h * k) -
      twistLogPrimitive t (g * h) k - twistLogPrimitive t g h := by
  letI := Fintype.ofFinite t.group
  exact averageThreeCochain_coboundary (twistLog t) (twistLog_cocycle ht) g h k

/-- Taking signs preserves the full signed pentagon. -/
theorem signTwistLaws : TwistLaws (signTwistData t) where
  nu_one_left := ht.nu_one_left
  nu_one_right := ht.nu_one_right
  omega_one₁ g h := by
    change unitSign (t.omega 1 g h) = 1
    rw [ht.omega_one₁, map_one]
  omega_one₂ g h := by
    change unitSign (t.omega g 1 h) = 1
    rw [ht.omega_one₂, map_one]
  omega_one₃ g h := by
    change unitSign (t.omega g h 1) = 1
    rw [ht.omega_one₃, map_one]
  cocycle := ht.cocycle
  pentagon g h k l := by
    have he := congrArg unitSign (ht.pentagon g h k l)
    simp only [map_mul, unitSign_realSign] at he
    exact he

/-- Exponentiating the average cancels precisely the positive magnitude. -/
theorem positiveGauge_ratio (g h k : t.group) :
    ((positiveGaugeData t).beta (g * h) k * (positiveGaugeData t).beta g h) *
      ((positiveGaugeData t).beta h k * (positiveGaugeData t).beta g (h * k))⁻¹ =
        (unitMagnitude (t.omega g h k))⁻¹ := by
  rw [← unitExp_unitLog]
  change (unitExp (Multiplicative.ofAdd (twistLogPrimitive t (g * h) k)) *
      unitExp (Multiplicative.ofAdd (twistLogPrimitive t g h))) *
      (unitExp (Multiplicative.ofAdd (twistLogPrimitive t h k)) *
        unitExp (Multiplicative.ofAdd (twistLogPrimitive t g (h * k))))⁻¹ =
      (unitExp (Multiplicative.ofAdd (twistLog t g h k)))⁻¹
  rw [← map_mul unitExp, ← map_mul unitExp, ← map_inv unitExp,
    ← map_mul unitExp, ← map_inv unitExp]
  apply congrArg unitExp
  change (twistLogPrimitive t (g * h) k + twistLogPrimitive t g h) +
      -(twistLogPrimitive t h k + twistLogPrimitive t g (h * k)) = -twistLog t g h k
  have he := twistLogPrimitive_coboundary ht g h k
  linarith

theorem positiveGaugeLaws : GaugeLaws t (signTwistData t) (positiveGaugeData t) where
  rho _ := rfl
  lam_one := rfl
  beta_one_left g := by
    change unitExp (Multiplicative.ofAdd (twistLogPrimitive t 1 g)) = 1
    rw [twistLogPrimitive_one_left ht]
    exact map_one unitExp
  beta_one_right g := by
    change unitExp (Multiplicative.ofAdd (twistLogPrimitive t g 1)) = 1
    rw [twistLogPrimitive_one_right ht]
    exact map_one unitExp
  nu g h := by
    change t.nu g h = t.nu g h + 0 + 0 + 0
    simp only [add_zero]
  omega g h k := by
    change unitSign (t.omega g h k) = t.omega g h k *
      ((positiveGaugeData t).beta (g * h) k * (positiveGaugeData t).beta g h) *
      ((positiveGaugeData t).beta h k * (positiveGaugeData t).beta g (h * k))⁻¹ *
      realSign (t.nu g h * 0 + 0 * t.nu h k)
    simp only [mul_zero, zero_mul, zero_add]
    rw [show realSign 0 = 1 from rfl, mul_one, mul_assoc, positiveGauge_ratio ht]
    exact unitSign_eq_div _

omit ht in
noncomputable def signTwist (t : Twist) : Twist where
  data := signTwistData t.data
  laws := signTwistLaws t.laws

omit ht in
/-- Every admissible real twist is gauge equivalent to an admissible
sign-valued twist. This lemma is independent of category reconstruction. -/
theorem exists_sign_twist (t : Twist) :
    ∃ s : Twist, (∀ g h k, s.data.omega g h k = 1 ∨ s.data.omega g h k = -1) ∧
      GaugeEquivalent t.data s.data := by
  refine ⟨signTwist t, fun g h k => unitSign_cases _, ?_⟩
  exact ⟨⟨positiveGaugeData t.data, positiveGaugeLaws t.laws⟩⟩

end RMod.Classification
