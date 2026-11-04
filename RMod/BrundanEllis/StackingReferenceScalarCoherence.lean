import RMod.BrundanEllis.StackingReferenceScalar

/-! Exact scalar equalities used when clearing the two reference hexagons.
They live first in the sign/exponent group and are then mapped to real units. -/
noncomputable section
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RMod.RawDCT

def normalizationCertificate (a b : ZMod 8) : DyadicUnit :=
  dyadic (normalizationBit a b) (normalizationExponent a b)
def associatorCertificate (a b c : ZMod 8) : DyadicUnit :=
  (dyadic (betaBit a b c) (2 * betaExponent a b c))⁻¹

def leftShortScalar (a b c : ZMod 8) : DyadicUnit :=
  associatorCertificate b c a * normalizationCertificate a (b + c) * associatorCertificate a b c

def leftLongScalar (a b c : ZMod 8) : DyadicUnit :=
  normalizationCertificate a c * associatorCertificate b a c * normalizationCertificate a b

/-- Clearing the dyadic denominator gives an equality in the exact certificate group. -/
theorem leftScalar_certificate (a b c : ZMod 8) :
    dyadic 0 (2 * ((-(leftScaleExponent a b c / 2)).toNat : ℤ)) * leftShortScalar a b c =
      dyadic (leftScaleBit a b c) (2 * ((leftScaleExponent a b c / 2).toNat : ℤ)) *
        leftLongScalar a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide +kernel

/-- An integral signed power in the certificate group has the expected real value. -/
theorem halfDyadicRealHom_nat (s : ZMod 2) (n : ℕ) :
    ((halfDyadicRealHom (dyadic s (2 * (n : ℤ))) : ℝˣ) : ℝ) =
      (((-1 : ℤ) ^ s.val * 2 ^ n : ℤ) : ℝ) := by
  rw [halfDyadicRealHom_value, zpow_mul]
  have htwo : Real.sqrt 2 ^ (2 : ℤ) = (2 : ℝ) := by
    rw [zpow_ofNat]
    exact Real.sq_sqrt (by norm_num)
  rw [htwo, zpow_natCast, paritySign_pow]
  push_cast
  rfl

@[simp] theorem normalizationCertificate_value (a b : ZMod 8) :
    ((halfDyadicRealHom (normalizationCertificate a b) : ℝˣ) : ℝ) = normalizingScalar a b :=
  (normalizingScalar_certificate a b).symm

@[simp] theorem associatorCertificate_value (a b c : ZMod 8) :
    ((halfDyadicRealHom (associatorCertificate a b c) : ℝˣ) : ℝ) = (associatorScale a b c : ℝ) := by
  rw [associatorCertificate, map_inv]
  exact (associatorScale_certificate a b c).symm

/-- Scalar equality matching the denominator-cleared left matrix equation. -/
theorem leftScalar_coherence (a b c : ZMod 8) :
    (negativeScale (leftScaleExponent a b c) : ℝ) *
        ((associatorScale b c a : ℝ) * normalizingScalar a (b + c) * (associatorScale a b c : ℝ)) =
      (((-1 : ℤ) ^ (leftScaleBit a b c).val * positiveScale (leftScaleExponent a b c) : ℤ) : ℝ) *
        (normalizingScalar a c * (associatorScale b a c : ℝ) * normalizingScalar a b) := by
  have h := congrArg (fun x : DyadicUnit => ((halfDyadicRealHom x : ℝˣ) : ℝ))
    (leftScalar_certificate a b c)
  simpa only [leftShortScalar, leftLongScalar, map_mul, Units.val_mul,
    halfDyadicRealHom_nat, normalizationCertificate_value, associatorCertificate_value,
    ZMod.val_zero, pow_zero, one_mul, positiveScale, negativeScale] using h

def rightLongScalar (a b c : ZMod 8) : DyadicUnit :=
  associatorCertificate c a b * normalizationCertificate a c *
    (associatorCertificate a c b)⁻¹ * normalizationCertificate b c * associatorCertificate a b c

/-- The second hexagon retains precisely its quadratic sign defect. -/
theorem rightScalar_certificate (a b c : ZMod 8) :
    dyadic 0 (2 * ((-(rightScaleExponent a b c / 2)).toNat : ℤ)) * normalizationCertificate (a + b) c =
      dyadic (rightScaleBit a b c) (2 * ((rightScaleExponent a b c / 2).toNat : ℤ)) *
        dyadic (rightDefect a b c) 0 * rightLongScalar a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide +kernel

/-- Real scalar version, before dividing by the stored inverse-connector denominator. -/
theorem rightScalar_coherence (a b c : ZMod 8) :
    (negativeScale (rightScaleExponent a b c) : ℝ) * normalizingScalar (a + b) c =
      (((-1 : ℤ) ^ (rightScaleBit a b c).val * positiveScale (rightScaleExponent a b c) : ℤ) : ℝ) *
        paritySign (rightDefect a b c) *
        ((associatorScale c a b : ℝ) * normalizingScalar a c * (associatorScale a c b : ℝ)⁻¹ *
          normalizingScalar b c * (associatorScale a b c : ℝ)) := by
  have h := congrArg (fun x : DyadicUnit => ((halfDyadicRealHom x : ℝˣ) : ℝ))
    (rightScalar_certificate a b c)
  simp only [rightLongScalar, map_mul, Units.val_mul, map_inv, Units.val_inv_eq_inv_val] at h
  rw [halfDyadicRealHom_nat, halfDyadicRealHom_nat] at h
  simpa only [normalizationCertificate_value, associatorCertificate_value,
    halfDyadicRealHom_value, zpow_zero, mul_one,
    ZMod.val_zero, pow_zero, one_mul, positiveScale, negativeScale] using h

end RMod.BrundanEllis.Stacking.ReferenceCommutor
