import RMod.BrundanEllis.StackingReferenceAssociatorData
import RMod.BrundanEllis.StackingReferenceCommutorEncoding
import RMod.BrundanEllis.StackingReferenceNormalizationData

/-! The two reference hexagons in finite coordinates. All connector and action
coefficients are read from the existing reference. Integer numerators keep
finite verification separate from extension of scalars to the real numbers. -/
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT
open RMod.ConstructiveConnectorTable RealPChiKernel

/-- Flat positions in the fixed row/coefficient order. -/
def leftPosition (a b c : ZMod 8) (i : LeftIndex a b c) : ℕ :=
  (i.1.val * fusionRank (a + b) c + i.2.1.val) * realRepDim (a + b + c).val + i.2.2.val

def rightPosition (a b c : ZMod 8) (i : RightIndex a b c) : ℕ :=
  (i.1.val * fusionRank a (b + c) + i.2.1.val) * realRepDim (a + b + c).val + i.2.2.val

/-- Full exchange entry, with natural-number indices for equal endpoint labels. -/
def exchangeEntry (a b : ZMod 8) (r u s v : ℕ) : ℤ :=
  if hr : r < fusionRank b a then
    if hu : u < realRepDim (b + a).val then
      if hs : s < fusionRank a b then
        if hv : v < realRepDim (a + b).val then
          forwardZ a b (⟨r, hr⟩, ⟨u, hu⟩) (⟨s, hs⟩, ⟨v, hv⟩)
        else 0
      else 0
    else 0
  else 0

/-- Exchange the inner pair on a left-associated route. -/
def innerLeftZ (a b c : ZMod 8) : Matrix (LeftIndex b a c) (LeftIndex a b c) ℤ :=
  fun r s => ∑ u : Fin (realRepDim (b + a).val),
    coefficientZ a b (forwardZ a b) r.1 s.1 u.val *
      ((-1 : ℤ) ^ (realComputableNuBeta.data.nu (Multiplicative.ofAdd (b + a))
        (Multiplicative.ofAdd c) * realRepBasisParity (b + a) u).val *
      fusionLeftSlotCoeff (b + a) c u.val r.2.1.val r.2.2.val s.2.1.val s.2.2.val)

/-- Exchange the inner pair on a right-associated route. -/
def innerRightZ (a b c : ZMod 8) : Matrix (RightIndex a c b) (RightIndex a b c) ℤ :=
  fun r s => ∑ u : Fin (realRepDim (c + b).val),
    coefficientZ b c (forwardZ b c) r.1 s.1 u.val *
      ((-1 : ℤ) ^ (realComputableNuBeta.data.nu (Multiplicative.ofAdd a)
        (Multiplicative.ofAdd (c + b)) * realRepBasisParity (c + b) u).val *
      fusionRightSlotCoeff a (c + b) u.val r.2.1.val r.2.2.val s.2.1.val s.2.2.val)

/-- Exchange the outer pair, retaining the inner row and its Koszul sign. -/
def outerRightZ (a b c : ZMod 8) : Matrix (LeftIndex b c a) (RightIndex a b c) ℤ :=
  fun r s => if r.1 = s.1 then
    (-1 : ℤ) ^ (degree a (b + c) * (FusionTable.indexParity b c s.1 +
      realComputableNuBeta.data.nu (Multiplicative.ofAdd b) (Multiplicative.ofAdd c))).val *
    exchangeEntry a (b + c) r.2.1.val r.2.2.val s.2.1.val s.2.2.val
  else 0

def outerLeftZ (a b c : ZMod 8) : Matrix (RightIndex c a b) (LeftIndex a b c) ℤ :=
  fun r s => if r.1 = s.1 then
    (-1 : ℤ) ^ (degree (a + b) c * (FusionTable.indexParity a b s.1 +
      realComputableNuBeta.data.nu (Multiplicative.ofAdd a) (Multiplicative.ofAdd b))).val *
    exchangeEntry (a + b) c r.2.1.val r.2.2.val s.2.1.val s.2.2.val
  else 0

/-- Numerator of the actual reverse connector in shifted coordinates. -/
def associatorInverseZ (a b c : ZMod 8) : Matrix (LeftIndex a b c) (RightIndex a b c) ℤ :=
  fun r s => leftFrameZ a b c r.1 *
    leftMulBasisCoeff (a + b + c).val
      (fun h => coeffGet (inverseNumeratorCoeff a b c)
        (sourceFramePosition a b c r.1.val r.2.1.val)
        (targetFramePosition a b c s.1.val s.2.1.val) h)
      s.2.2.val r.2.2.val * rightFrameZ a b c s.1

/-- Forward-connector form of the first hexagon, with no inverse connector. -/
def leftShortZ (a b c : ZMod 8) : Matrix (RightIndex b c a) (LeftIndex a b c) ℤ :=
  associatorZ b c a * outerRightZ a b c * associatorZ a b c

def leftLongZ (a b c : ZMod 8) : Matrix (RightIndex b c a) (LeftIndex a b c) ℤ :=
  innerRightZ b a c * associatorZ b a c * innerLeftZ a b c

/-- The long side of the second hexagon; the inverse denominator is kept separate. -/
def rightLongZ (a b c : ZMod 8) : Matrix (RightIndex c a b) (LeftIndex a b c) ℤ :=
  associatorZ c a b * innerLeftZ a c b * associatorInverseZ a c b *
    innerRightZ a b c * associatorZ a b c

/-- The binary scalar and reference beta are represented as sign and sqrt(2) exponent. -/
def normalizationBit (a b : ZMod 8) : ZMod 2 := if normalizationNegative a b then 1 else 0
def betaBit (a b c : ZMod 8) : ZMod 2 :=
  (GaugeChi.realLeanBetaTable (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
    (Multiplicative.ofAdd c)).toAdd.1
def betaExponent (a b c : ZMod 8) : ℤ :=
  (GaugeChi.realLeanBetaTable (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
    (Multiplicative.ofAdd c)).toAdd.2

def leftScaleExponent (a b c : ZMod 8) : ℤ :=
  normalizationExponent a (b + c) - normalizationExponent a b - normalizationExponent a c -
    2 * betaExponent b c a - 2 * betaExponent a b c + 2 * betaExponent b a c

def leftScaleBit (a b c : ZMod 8) : ZMod 2 :=
  normalizationBit a (b + c) + normalizationBit a b + normalizationBit a c +
    betaBit b c a + betaBit a b c + betaBit b a c

def rightScaleExponent (a b c : ZMod 8) : ℤ :=
  normalizationExponent (a + b) c - normalizationExponent a c - normalizationExponent b c +
    2 * betaExponent c a b - 2 * betaExponent a c b + 2 * betaExponent a b c

/-- The predicted super hexagon defect has the quadratic primitive in the last label. -/
def rightDefect (a b c : ZMod 8) : ZMod 2 :=
  (a.val : ZMod 2) * (b.val : ZMod 2) * ((c.val * (c.val + 1) / 2 : ℕ) : ZMod 2)

def rightScaleBit (a b c : ZMod 8) : ZMod 2 :=
  normalizationBit (a + b) c + normalizationBit a c + normalizationBit b c +
    betaBit c a b + betaBit a c b + betaBit a b c + rightDefect a b c

/-- Clear a possibly negative dyadic exponent without dividing in the integers. -/
def positiveScale (e : ℤ) : ℤ := 2 ^ (e / 2).toNat
def negativeScale (e : ℤ) : ℤ := 2 ^ (-(e / 2)).toNat

/-- Finite coefficient equations expected from the normalized hexagons. -/
def LeftEquation (a b c : ZMod 8) : Prop :=
  ((-1 : ℤ) ^ (leftScaleBit a b c).val * positiveScale (leftScaleExponent a b c)) •
      leftShortZ a b c = negativeScale (leftScaleExponent a b c) • leftLongZ a b c

def RightEquation (a b c : ZMod 8) : Prop :=
  ((-1 : ℤ) ^ (rightScaleBit a b c).val * positiveScale (rightScaleExponent a b c) *
    (inverseScale a c b : ℤ)) • outerLeftZ a b c =
      negativeScale (rightScaleExponent a b c) • rightLongZ a b c

end RMod.BrundanEllis.Stacking.ReferenceCommutor
