import RMod.BrundanEllis.StackingReferenceHexagonData
import RMod.BrundanEllis.StackingReferenceNormalization

/-! Exact scalar certificates for the square-root normalizations. The certificate
group is an existing additive sign/exponent group, realized in real units. -/
noncomputable section
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RMod.RawDCT

/-- The positive square root of two as a real unit. -/
def sqrtTwoUnit : ℝˣ := Units.mk0 (Real.sqrt 2) (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))

/-- Realize a sign and an integer exponent as a signed power of sqrt(2). -/
def halfDyadicRealHom : DyadicUnit →* ℝˣ where
  toFun x := (sgn x.toAdd.1 : ℝˣ) * sqrtTwoUnit ^ x.toAdd.2
  map_one' := by simp
  map_mul' x y := by
    change (sgn (x.toAdd.1 + y.toAdd.1) : ℝˣ) * sqrtTwoUnit ^ (x.toAdd.2 + y.toAdd.2) = _
    rw [sgn_add, zpow_add]
    exact mul_mul_mul_comm _ _ _ _

@[simp] theorem coe_sgn_paritySign (s : ZMod 2) : ((sgn s : ℝˣ) : ℝ) = paritySign s := by
  rcases zmod2_cases s with rfl | rfl <;> rfl

@[simp] theorem halfDyadicRealHom_value (s : ZMod 2) (e : ℤ) :
    ((halfDyadicRealHom (dyadic s e) : ℝˣ) : ℝ) = paritySign s * (Real.sqrt 2) ^ e := by
  simp [halfDyadicRealHom, dyadic, sqrtTwoUnit]

/-- The normalization is the value of its exact sign/exponent certificate. -/
theorem normalizingScalar_certificate (a b : ZMod 8) :
    normalizingScalar a b =
      ((halfDyadicRealHom (dyadic (normalizationBit a b) (normalizationExponent a b)) : ℝˣ) : ℝ) := by
  rw [halfDyadicRealHom_value]
  unfold normalizingScalar normalizationBit
  cases normalizationNegative a b <;> rfl

/-- Integral powers of two are the even powers of the positive square root. -/
theorem sqrtTwoUnit_sq : sqrtTwoUnit ^ (2 : ℤ) = Units.mk0 (2 : ℝ) (by norm_num) := by
  apply Units.ext
  change (Real.sqrt 2) ^ (2 : ℤ) = (2 : ℝ)
  rw [zpow_ofNat]
  exact Real.sq_sqrt (by norm_num)

/-- The old dyadic realization is the even-exponent part of the new one. -/
theorem halfDyadicRealHom_even (s : ZMod 2) (e : ℤ) :
    halfDyadicRealHom (dyadic s (2 * e)) = dyadicRealHom (dyadic s e) := by
  apply Units.ext
  rw [halfDyadicRealHom_value]
  change paritySign s * Real.sqrt 2 ^ (2 * e) = (dyadicRatValue (dyadic s e) : ℝ)
  rw [dyadicRatValue_dyadic, Rat.cast_mul, Rat.cast_zpow]
  have hs : (((sgn s : ℚˣ) : ℚ) : ℝ) = paritySign s := by
    rcases zmod2_cases s with rfl | rfl <;> norm_num [sgn, paritySign]
  rw [hs, zpow_mul]
  have htwo : Real.sqrt 2 ^ (2 : ℤ) = (2 : ℝ) := by
    rw [zpow_ofNat]
    exact Real.sq_sqrt (by norm_num)
  rw [htwo]
  norm_num

/-- The inverse reference beta is represented with twice its dyadic exponent. -/
theorem associatorScale_certificate (a b c : ZMod 8) :
    (associatorScale a b c : ℝ) =
      ((halfDyadicRealHom (dyadic (betaBit a b c) (2 * betaExponent a b c)))⁻¹ : ℝˣ) := by
  rw [halfDyadicRealHom_even]
  let d := GaugeChi.realLeanBetaTable (Multiplicative.ofAdd a)
    (Multiplicative.ofAdd b) (Multiplicative.ofAdd c)
  change (↑((dyadicRatValue d)⁻¹) : ℝ) = (↑(dyadicRatValue d⁻¹) : ℝ)
  rw [dyadicRatValue_inv]

/-- The exponent differences in both normalized hexagons are even. -/
theorem hexagon_scale_even (a b c : ZMod 8) :
    leftScaleExponent a b c % 2 = 0 ∧ rightScaleExponent a b c % 2 = 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor
