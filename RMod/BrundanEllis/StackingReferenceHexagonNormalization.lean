import RMod.BrundanEllis.StackingReferenceScalarCoherence

/-! Lift the denominator-cleared integer hexagons to real matrix identities.
The finite equations remain explicit hypotheses here; the certificate modules
supply them without adding assumptions to the eventual categorical theorem. -/
noncomputable section
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RMod.RawDCT

private theorem negativeScale_cast_ne_zero (e : ℤ) : (negativeScale e : ℝ) ≠ 0 := by
  unfold negativeScale
  rw [Int.cast_pow]
  exact pow_ne_zero _ (by norm_num)

/-- Normalizing the first integer hexagon gives exact equality over the reals. -/
theorem leftHexagon_normalized (a b c : ZMod 8) (h : LeftEquation a b c) :
    ((associatorScale b c a : ℝ) * normalizingScalar a (b + c) * (associatorScale a b c : ℝ)) •
        (leftShortZ a b c).map ((↑) : ℤ → ℝ) =
      (normalizingScalar a c * (associatorScale b a c : ℝ) * normalizingScalar a b) •
        (leftLongZ a b c).map ((↑) : ℤ → ℝ) := by
  ext i j
  have hm := congrArg (fun M : Matrix (RightIndex b c a) (LeftIndex a b c) ℤ => (M i j : ℝ)) h
  change (↑(((-1 : ℤ) ^ (leftScaleBit a b c).val * positiveScale (leftScaleExponent a b c)) *
      leftShortZ a b c i j) : ℝ) =
    (↑(negativeScale (leftScaleExponent a b c) * leftLongZ a b c i j) : ℝ) at hm
  simp only [Int.cast_mul] at hm
  have hs := leftScalar_coherence a b c
  simp only [Int.cast_mul] at hs
  apply mul_left_cancel₀ (negativeScale_cast_ne_zero (leftScaleExponent a b c))
  change (negativeScale (leftScaleExponent a b c) : ℝ) *
    (((associatorScale b c a : ℝ) * normalizingScalar a (b + c) * (associatorScale a b c : ℝ)) *
      (leftShortZ a b c i j : ℝ)) = _
  rw [← mul_assoc, hs]
  have hm' := congrArg (fun q : ℝ =>
    (normalizingScalar a c * (associatorScale b a c : ℝ) * normalizingScalar a b) * q) hm
  change _ = (negativeScale (leftScaleExponent a b c) : ℝ) *
    ((normalizingScalar a c * (associatorScale b a c : ℝ) * normalizingScalar a b) *
      (leftLongZ a b c i j : ℝ))
  linear_combination hm'

/-- Normalizing the second hexagon leaves exactly the specified parity sign. -/
theorem rightHexagon_normalized (a b c : ZMod 8) (h : RightEquation a b c) :
    ((RMod.ConstructiveConnectorTable.inverseScale a c b : ℝ) * normalizingScalar (a + b) c) •
        (outerLeftZ a b c).map ((↑) : ℤ → ℝ) =
      (paritySign (rightDefect a b c) *
        ((associatorScale c a b : ℝ) * normalizingScalar a c * (associatorScale a c b : ℝ)⁻¹ *
          normalizingScalar b c * (associatorScale a b c : ℝ))) •
        (rightLongZ a b c).map ((↑) : ℤ → ℝ) := by
  ext i j
  have hm := congrArg (fun M : Matrix (RightIndex c a b) (LeftIndex a b c) ℤ => (M i j : ℝ)) h
  change (↑(((-1 : ℤ) ^ (rightScaleBit a b c).val * positiveScale (rightScaleExponent a b c) *
      (RMod.ConstructiveConnectorTable.inverseScale a c b : ℤ)) * outerLeftZ a b c i j) : ℝ) =
    (↑(negativeScale (rightScaleExponent a b c) * rightLongZ a b c i j) : ℝ) at hm
  simp only [Int.cast_mul, Int.cast_natCast] at hm
  have hs := rightScalar_coherence a b c
  simp only [Int.cast_mul] at hs
  apply mul_left_cancel₀ (negativeScale_cast_ne_zero (rightScaleExponent a b c))
  change (negativeScale (rightScaleExponent a b c) : ℝ) *
      (((RMod.ConstructiveConnectorTable.inverseScale a c b : ℝ) * normalizingScalar (a + b) c) *
        (outerLeftZ a b c i j : ℝ)) =
    (negativeScale (rightScaleExponent a b c) : ℝ) *
      ((paritySign (rightDefect a b c) *
        ((associatorScale c a b : ℝ) * normalizingScalar a c * (associatorScale a c b : ℝ)⁻¹ *
          normalizingScalar b c * (associatorScale a b c : ℝ))) * (rightLongZ a b c i j : ℝ))
  linear_combination
    (RMod.ConstructiveConnectorTable.inverseScale a c b : ℝ) * (outerLeftZ a b c i j : ℝ) * hs +
    paritySign (rightDefect a b c) *
      ((associatorScale c a b : ℝ) * normalizingScalar a c * (associatorScale a c b : ℝ)⁻¹ *
        normalizingScalar b c * (associatorScale a b c : ℝ)) * hm

end RMod.BrundanEllis.Stacking.ReferenceCommutor
