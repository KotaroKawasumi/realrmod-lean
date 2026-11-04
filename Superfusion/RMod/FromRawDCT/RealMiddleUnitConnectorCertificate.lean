import Superfusion.RMod.FromRawDCT.RealCandidate
import Superfusion.Gauge.RealFuseSpecPilot

/-!
# Raw middle-unit connector certificate

This file isolates the only finite connector-table calculation used by the
real triangle proof.  It checks the 64 triples `(a, 0, c)` against the actual
stored forward connector.  No fourfold route or pentagon composite is formed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace Superfusion.RMod.FromRawDCT

open RawDCT
open RModCoordinate
open RModCoordinate.FusionTable

attribute [local simp] ZMod.val_zero

namespace RealMiddleUnitConnectorCertificate

/-! ## Statement of the raw middle-unit certificate -/

/-- The raw computable `DCT` whose frozen connector table is certified. -/
abbrev rawX : RawDCTData := realRawDCT.data

/-- At one closed pair `(a,c)`, the raw connector `T(a,0,c)` is the identity
after the two outer fusion rows are transported to the common row `C(a,c)`.
This is a statement about the actual raw connector entry, not an auxiliary
table-valued associator. -/
private def ForwardIdentityAtPair (a c : ZMod 8) : Prop :=
  ∀ (sourceAB : rawX.C.Index a 0)
    (sourceABC : rawX.C.Index (a + 0) c)
    (targetBC : rawX.C.Index 0 c)
    (targetABC : rawX.C.Index a (0 + c)),
    realTForwardEntry a 0 c targetBC targetABC sourceAB sourceABC =
      if Associator.castIndex rawX (add_zero a) rfl sourceABC =
          Associator.castIndex rawX rfl (zero_add c) targetABC then
        Coeff.one (a + 0 + c)
      else Coeff.zero (a + 0 + c)

/-- A first-label slice consists of its eight closed second-label pairs. -/
private def ForwardIdentityAt (a : ZMod 8) : Prop :=
  ∀ c : ZMod 8, ForwardIdentityAtPair a c

/-! The literal slices below reuse the standard values of the eight
representatives; these lemmas only remove `ZMod.val` transports. -/

@[simp] private theorem zmod8_val_zero : (0 : ZMod 8).val = 0 := by
  exact ZMod.val_natCast_of_lt (by norm_num)

@[simp] private theorem zmod8_val_one : (1 : ZMod 8).val = 1 := by
  exact ZMod.val_natCast_of_lt (by norm_num)

@[simp] private theorem zmod8_val_two : (2 : ZMod 8).val = 2 := by
  exact ZMod.val_natCast_of_lt (by norm_num)

@[simp] private theorem zmod8_val_three : (3 : ZMod 8).val = 3 := by
  exact ZMod.val_natCast_of_lt (by norm_num)

@[simp] private theorem zmod8_val_four : (4 : ZMod 8).val = 4 := by
  exact ZMod.val_natCast_of_lt (by norm_num)

@[simp] private theorem zmod8_val_five : (5 : ZMod 8).val = 5 := by
  exact ZMod.val_natCast_of_lt (by norm_num)

@[simp] private theorem zmod8_val_six : (6 : ZMod 8).val = 6 := by
  exact ZMod.val_natCast_of_lt (by norm_num)

@[simp] private theorem zmod8_val_seven : (7 : ZMod 8).val = 7 := by
  exact ZMod.val_natCast_of_lt (by norm_num)

/-! On a middle-unit face, three of the four binary fusion sizes are
unit sizes.  Keeping these existing table consequences opaque prevents the
large `realSizeAux` match from being duplicated in every connector goal. -/

@[simp] private theorem realSize_zero_left_certificate (c : ZMod 8) :
    Superfusion.realSize 0 c = (1, 0) := by
  rfl

@[simp] private theorem realSize_zero_right_certificate (a : ZMod 8) :
    Superfusion.realSize a 0 = (1, 0) := by
  fin_cases a <;> rfl

/-! The non-unit binary size in each closed `a = 1` pair is read directly
from the already stored `realSize` table. -/

@[simp] private theorem realSize_one_zero_certificate :
    Superfusion.realSize 1 0 = (1, 0) := by rfl

@[simp] private theorem realSize_one_one_certificate :
    Superfusion.realSize 1 1 = (1, 0) := by rfl

@[simp] private theorem realSize_one_two_certificate :
    Superfusion.realSize 1 2 = (1, 0) := by rfl

@[simp] private theorem realSize_one_three_certificate :
    Superfusion.realSize 1 3 = (1, 1) := by rfl

@[simp] private theorem realSize_one_four_certificate :
    Superfusion.realSize 1 4 = (1, 0) := by rfl

@[simp] private theorem realSize_one_five_certificate :
    Superfusion.realSize 1 5 = (1, 1) := by rfl

@[simp] private theorem realSize_one_six_certificate :
    Superfusion.realSize 1 6 = (1, 1) := by rfl

@[simp] private theorem realSize_one_seven_certificate :
    Superfusion.realSize 1 7 = (1, 1) := by rfl

/-! The non-unit binary sizes in the `a = 2` slice are the stored size-table row. -/

@[simp] private theorem realSize_two_zero_certificate :
    Superfusion.realSize 2 0 = (1, 0) := by rfl

@[simp] private theorem realSize_two_one_certificate :
    Superfusion.realSize 2 1 = (1, 0) := by rfl

@[simp] private theorem realSize_two_two_certificate :
    Superfusion.realSize 2 2 = (1, 1) := by rfl

@[simp] private theorem realSize_two_three_certificate :
    Superfusion.realSize 2 3 = (1, 1) := by rfl

@[simp] private theorem realSize_two_four_certificate :
    Superfusion.realSize 2 4 = (1, 1) := by rfl

@[simp] private theorem realSize_two_five_certificate :
    Superfusion.realSize 2 5 = (2, 2) := by rfl

@[simp] private theorem realSize_two_six_certificate :
    Superfusion.realSize 2 6 = (2, 2) := by rfl

@[simp] private theorem realSize_two_seven_certificate :
    Superfusion.realSize 2 7 = (1, 1) := by rfl

/-! The remaining non-unit binary sizes are closed readings of the stored
`realSize` table; no connector or coherence expression is evaluated here. -/

@[simp] private theorem realSize_three_zero_certificate :
    Superfusion.realSize 3 0 = (1, 0) := by rfl

@[simp] private theorem realSize_three_one_certificate :
    Superfusion.realSize 3 1 = (1, 1) := by rfl

@[simp] private theorem realSize_three_two_certificate :
    Superfusion.realSize 3 2 = (1, 1) := by rfl

@[simp] private theorem realSize_three_three_certificate :
    Superfusion.realSize 3 3 = (2, 2) := by rfl

@[simp] private theorem realSize_three_four_certificate :
    Superfusion.realSize 3 4 = (2, 2) := by rfl

@[simp] private theorem realSize_three_five_certificate :
    Superfusion.realSize 3 5 = (4, 4) := by rfl

@[simp] private theorem realSize_three_six_certificate :
    Superfusion.realSize 3 6 = (2, 2) := by rfl

@[simp] private theorem realSize_three_seven_certificate :
    Superfusion.realSize 3 7 = (1, 1) := by rfl

@[simp] private theorem realSize_four_zero_certificate :
    Superfusion.realSize 4 0 = (1, 0) := by rfl

@[simp] private theorem realSize_four_one_certificate :
    Superfusion.realSize 4 1 = (1, 0) := by rfl

@[simp] private theorem realSize_four_two_certificate :
    Superfusion.realSize 4 2 = (1, 1) := by rfl

@[simp] private theorem realSize_four_three_certificate :
    Superfusion.realSize 4 3 = (2, 2) := by rfl

@[simp] private theorem realSize_four_four_certificate :
    Superfusion.realSize 4 4 = (4, 0) := by rfl

@[simp] private theorem realSize_four_five_certificate :
    Superfusion.realSize 4 5 = (2, 2) := by rfl

@[simp] private theorem realSize_four_six_certificate :
    Superfusion.realSize 4 6 = (1, 1) := by rfl

@[simp] private theorem realSize_four_seven_certificate :
    Superfusion.realSize 4 7 = (1, 0) := by rfl

@[simp] private theorem realSize_five_zero_certificate :
    Superfusion.realSize 5 0 = (1, 0) := by rfl

@[simp] private theorem realSize_five_one_certificate :
    Superfusion.realSize 5 1 = (1, 1) := by rfl

@[simp] private theorem realSize_five_two_certificate :
    Superfusion.realSize 5 2 = (2, 2) := by rfl

@[simp] private theorem realSize_five_three_certificate :
    Superfusion.realSize 5 3 = (4, 4) := by rfl

@[simp] private theorem realSize_five_four_certificate :
    Superfusion.realSize 5 4 = (2, 2) := by rfl

@[simp] private theorem realSize_five_five_certificate :
    Superfusion.realSize 5 5 = (2, 2) := by rfl

@[simp] private theorem realSize_five_six_certificate :
    Superfusion.realSize 5 6 = (1, 1) := by rfl

@[simp] private theorem realSize_five_seven_certificate :
    Superfusion.realSize 5 7 = (1, 1) := by rfl

@[simp] private theorem realSize_six_zero_certificate :
    Superfusion.realSize 6 0 = (1, 0) := by rfl

@[simp] private theorem realSize_six_one_certificate :
    Superfusion.realSize 6 1 = (1, 1) := by rfl

@[simp] private theorem realSize_six_two_certificate :
    Superfusion.realSize 6 2 = (2, 2) := by rfl

@[simp] private theorem realSize_six_three_certificate :
    Superfusion.realSize 6 3 = (2, 2) := by rfl

@[simp] private theorem realSize_six_four_certificate :
    Superfusion.realSize 6 4 = (1, 1) := by rfl

@[simp] private theorem realSize_six_five_certificate :
    Superfusion.realSize 6 5 = (1, 1) := by rfl

@[simp] private theorem realSize_six_six_certificate :
    Superfusion.realSize 6 6 = (1, 1) := by rfl

@[simp] private theorem realSize_six_seven_certificate :
    Superfusion.realSize 6 7 = (1, 0) := by rfl

@[simp] private theorem realSize_seven_zero_certificate :
    Superfusion.realSize 7 0 = (1, 0) := by rfl

@[simp] private theorem realSize_seven_one_certificate :
    Superfusion.realSize 7 1 = (1, 1) := by rfl

@[simp] private theorem realSize_seven_two_certificate :
    Superfusion.realSize 7 2 = (1, 1) := by rfl

@[simp] private theorem realSize_seven_three_certificate :
    Superfusion.realSize 7 3 = (1, 1) := by rfl

@[simp] private theorem realSize_seven_four_certificate :
    Superfusion.realSize 7 4 = (1, 0) := by rfl

@[simp] private theorem realSize_seven_five_certificate :
    Superfusion.realSize 7 5 = (1, 1) := by rfl

@[simp] private theorem realSize_seven_six_certificate :
    Superfusion.realSize 7 6 = (1, 0) := by rfl

@[simp] private theorem realSize_seven_seven_certificate :
    Superfusion.realSize 7 7 = (1, 0) := by rfl





/-! Endpoint transport does not change the numerical fusion-row position.
This is pure equality elimination and inspects no connector entry. -/

@[simp] private theorem castIndex_val_certificate (x : RawDCTData)
    {a b a' b' : ZMod 8} (ha : a = a') (hb : b = b')
    (r : x.C.Index a b) :
    (Associator.castIndex x ha hb r).val = r.val := by
  subst a'
  subst b'
  rfl

/-! ## The eight closed pairs in the `a = 0` slice -/

private theorem forwardIdentityAt_zero_zero : ForwardIdentityAtPair 0 0 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB
  fin_cases sourceABC
  fin_cases targetBC
  fin_cases targetABC
  rw [if_pos (by apply Fin.ext; rfl)]
  funext e
  fin_cases e
  all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Coeff.one,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_0_0_0,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_zero_one : ForwardIdentityAtPair 0 1 := by
  have hcval : (1 : ZMod 8).val = 1 := by
    exact ZMod.val_natCast_of_lt (by norm_num)
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB
  fin_cases sourceABC
  fin_cases targetBC
  fin_cases targetABC
  rw [if_pos (by apply Fin.ext; rfl)]
  funext e
  fin_cases e
  all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Coeff.one,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_0_0_1,
      Superfusion.coeffGet, Superfusion.realRepDim, hcval]

private theorem forwardIdentityAt_zero_two : ForwardIdentityAtPair 0 2 := by
  have hcval : (2 : ZMod 8).val = 2 := by
    exact ZMod.val_natCast_of_lt (by norm_num)
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB
  fin_cases sourceABC
  fin_cases targetBC
  fin_cases targetABC
  rw [if_pos (by apply Fin.ext; rfl)]
  funext e
  fin_cases e
  all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Coeff.one,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_0_0_2,
      Superfusion.coeffGet, Superfusion.realRepDim, hcval]

private theorem forwardIdentityAt_zero_three : ForwardIdentityAtPair 0 3 := by
  have hcval : (3 : ZMod 8).val = 3 := by
    exact ZMod.val_natCast_of_lt (by norm_num)
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB
  fin_cases sourceABC
  fin_cases targetBC
  fin_cases targetABC
  rw [if_pos (by apply Fin.ext; rfl)]
  funext e
  fin_cases e
  all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Coeff.one,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_0_0_3,
      Superfusion.coeffGet, Superfusion.realRepDim, hcval]

private theorem forwardIdentityAt_zero_four : ForwardIdentityAtPair 0 4 := by
  have hcval : (4 : ZMod 8).val = 4 := by
    exact ZMod.val_natCast_of_lt (by norm_num)
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB
  fin_cases sourceABC
  fin_cases targetBC
  fin_cases targetABC
  rw [if_pos (by apply Fin.ext; rfl)]
  funext e
  fin_cases e
  all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Coeff.one,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_0_0_4,
      Superfusion.coeffGet, Superfusion.realRepDim, hcval]

private theorem forwardIdentityAt_zero_five : ForwardIdentityAtPair 0 5 := by
  have hcval : (5 : ZMod 8).val = 5 := by
    exact ZMod.val_natCast_of_lt (by norm_num)
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB
  fin_cases sourceABC
  fin_cases targetBC
  fin_cases targetABC
  rw [if_pos (by apply Fin.ext; rfl)]
  funext e
  fin_cases e
  all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Coeff.one,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_0_0_5,
      Superfusion.coeffGet, Superfusion.realRepDim, hcval]

private theorem forwardIdentityAt_zero_six : ForwardIdentityAtPair 0 6 := by
  have hcval : (6 : ZMod 8).val = 6 := by
    exact ZMod.val_natCast_of_lt (by norm_num)
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB
  fin_cases sourceABC
  fin_cases targetBC
  fin_cases targetABC
  rw [if_pos (by apply Fin.ext; rfl)]
  funext e
  fin_cases e
  all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Coeff.one,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_0_0_6,
      Superfusion.coeffGet, Superfusion.realRepDim, hcval]

private theorem forwardIdentityAt_zero_seven : ForwardIdentityAtPair 0 7 := by
  have hcval : (7 : ZMod 8).val = 7 := by
    exact ZMod.val_natCast_of_lt (by norm_num)
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB
  fin_cases sourceABC
  fin_cases targetBC
  fin_cases targetABC
  rw [if_pos (by apply Fin.ext; rfl)]
  funext e
  fin_cases e
  all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Coeff.one,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_0_0_7,
      Superfusion.coeffGet, Superfusion.realRepDim, hcval]

private theorem forwardIdentityAt_zero : ForwardIdentityAt 0 := by
  intro c
  fin_cases c
  · exact forwardIdentityAt_zero_zero
  · exact forwardIdentityAt_zero_one
  · exact forwardIdentityAt_zero_two
  · exact forwardIdentityAt_zero_three
  · exact forwardIdentityAt_zero_four
  · exact forwardIdentityAt_zero_five
  · exact forwardIdentityAt_zero_six
  · exact forwardIdentityAt_zero_seven

/-! ## The remaining seven first-label slices -/

private theorem forwardIdentityAt_one_zero :
    ForwardIdentityAtPair 1 0 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_1_0_0,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_one_one :
    ForwardIdentityAtPair 1 1 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_1_0_1,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_one_two :
    ForwardIdentityAtPair 1 2 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_1_0_2,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_one_three :
    ForwardIdentityAtPair 1 3 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_1_0_3,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_one_four :
    ForwardIdentityAtPair 1 4 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_1_0_4,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_one_five :
    ForwardIdentityAtPair 1 5 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_1_0_5,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_one_six :
    ForwardIdentityAtPair 1 6 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_1_0_6,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_one_seven :
    ForwardIdentityAtPair 1 7 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_1_0_7,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_one : ForwardIdentityAt 1 := by
  intro c
  fin_cases c
  · exact forwardIdentityAt_one_zero
  · exact forwardIdentityAt_one_one
  · exact forwardIdentityAt_one_two
  · exact forwardIdentityAt_one_three
  · exact forwardIdentityAt_one_four
  · exact forwardIdentityAt_one_five
  · exact forwardIdentityAt_one_six
  · exact forwardIdentityAt_one_seven
private theorem forwardIdentityAt_two_zero :
    ForwardIdentityAtPair 2 0 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_2_0_0,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_two_one :
    ForwardIdentityAtPair 2 1 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_2_0_1,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_two_two :
    ForwardIdentityAtPair 2 2 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_2_0_2,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_two_three :
    ForwardIdentityAtPair 2 3 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_2_0_3,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_two_four :
    ForwardIdentityAtPair 2 4 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_2_0_4,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_two_five :
    ForwardIdentityAtPair 2 5 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_2_0_5,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_two_six :
    ForwardIdentityAtPair 2 6 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_2_0_6,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_two_seven :
    ForwardIdentityAtPair 2 7 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_2_0_7,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_two : ForwardIdentityAt 2 := by
  intro c
  fin_cases c
  · exact forwardIdentityAt_two_zero
  · exact forwardIdentityAt_two_one
  · exact forwardIdentityAt_two_two
  · exact forwardIdentityAt_two_three
  · exact forwardIdentityAt_two_four
  · exact forwardIdentityAt_two_five
  · exact forwardIdentityAt_two_six
  · exact forwardIdentityAt_two_seven


private theorem forwardIdentityAt_three_zero :
    ForwardIdentityAtPair 3 0 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_3_0_0,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_three_one :
    ForwardIdentityAtPair 3 1 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_3_0_1,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_three_two :
    ForwardIdentityAtPair 3 2 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_3_0_2,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_three_three :
    ForwardIdentityAtPair 3 3 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_3_0_3,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_three_four :
    ForwardIdentityAtPair 3 4 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_3_0_4,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_three_five :
    ForwardIdentityAtPair 3 5 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_3_0_5,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_three_six :
    ForwardIdentityAtPair 3 6 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_3_0_6,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_three_seven :
    ForwardIdentityAtPair 3 7 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_3_0_7,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_three : ForwardIdentityAt 3 := by
  intro c
  fin_cases c
  · exact forwardIdentityAt_three_zero
  · exact forwardIdentityAt_three_one
  · exact forwardIdentityAt_three_two
  · exact forwardIdentityAt_three_three
  · exact forwardIdentityAt_three_four
  · exact forwardIdentityAt_three_five
  · exact forwardIdentityAt_three_six
  · exact forwardIdentityAt_three_seven

private theorem forwardIdentityAt_four_zero :
    ForwardIdentityAtPair 4 0 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_4_0_0,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_four_one :
    ForwardIdentityAtPair 4 1 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_4_0_1,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_four_two :
    ForwardIdentityAtPair 4 2 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_4_0_2,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_four_three :
    ForwardIdentityAtPair 4 3 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_4_0_3,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_four_four :
    ForwardIdentityAtPair 4 4 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_4_0_4,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_four_five :
    ForwardIdentityAtPair 4 5 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_4_0_5,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_four_six :
    ForwardIdentityAtPair 4 6 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_4_0_6,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_four_seven :
    ForwardIdentityAtPair 4 7 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_4_0_7,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_four : ForwardIdentityAt 4 := by
  intro c
  fin_cases c
  · exact forwardIdentityAt_four_zero
  · exact forwardIdentityAt_four_one
  · exact forwardIdentityAt_four_two
  · exact forwardIdentityAt_four_three
  · exact forwardIdentityAt_four_four
  · exact forwardIdentityAt_four_five
  · exact forwardIdentityAt_four_six
  · exact forwardIdentityAt_four_seven

private theorem forwardIdentityAt_five_zero :
    ForwardIdentityAtPair 5 0 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_5_0_0,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_five_one :
    ForwardIdentityAtPair 5 1 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_5_0_1,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_five_two :
    ForwardIdentityAtPair 5 2 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_5_0_2,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_five_three :
    ForwardIdentityAtPair 5 3 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_5_0_3,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_five_four :
    ForwardIdentityAtPair 5 4 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_5_0_4,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_five_five :
    ForwardIdentityAtPair 5 5 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_5_0_5,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_five_six :
    ForwardIdentityAtPair 5 6 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_5_0_6,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_five_seven :
    ForwardIdentityAtPair 5 7 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_5_0_7,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_five : ForwardIdentityAt 5 := by
  intro c
  fin_cases c
  · exact forwardIdentityAt_five_zero
  · exact forwardIdentityAt_five_one
  · exact forwardIdentityAt_five_two
  · exact forwardIdentityAt_five_three
  · exact forwardIdentityAt_five_four
  · exact forwardIdentityAt_five_five
  · exact forwardIdentityAt_five_six
  · exact forwardIdentityAt_five_seven

private theorem forwardIdentityAt_six_zero :
    ForwardIdentityAtPair 6 0 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_6_0_0,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_six_one :
    ForwardIdentityAtPair 6 1 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_6_0_1,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_six_two :
    ForwardIdentityAtPair 6 2 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_6_0_2,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_six_three :
    ForwardIdentityAtPair 6 3 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_6_0_3,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_six_four :
    ForwardIdentityAtPair 6 4 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_6_0_4,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_six_five :
    ForwardIdentityAtPair 6 5 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_6_0_5,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_six_six :
    ForwardIdentityAtPair 6 6 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_6_0_6,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_six_seven :
    ForwardIdentityAtPair 6 7 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_6_0_7,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_six : ForwardIdentityAt 6 := by
  intro c
  fin_cases c
  · exact forwardIdentityAt_six_zero
  · exact forwardIdentityAt_six_one
  · exact forwardIdentityAt_six_two
  · exact forwardIdentityAt_six_three
  · exact forwardIdentityAt_six_four
  · exact forwardIdentityAt_six_five
  · exact forwardIdentityAt_six_six
  · exact forwardIdentityAt_six_seven

private theorem forwardIdentityAt_seven_zero :
    ForwardIdentityAtPair 7 0 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_7_0_0,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_seven_one :
    ForwardIdentityAtPair 7 1 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_7_0_1,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_seven_two :
    ForwardIdentityAtPair 7 2 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_7_0_2,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_seven_three :
    ForwardIdentityAtPair 7 3 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_7_0_3,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_seven_four :
    ForwardIdentityAtPair 7 4 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_7_0_4,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_seven_five :
    ForwardIdentityAtPair 7 5 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_7_0_5,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_seven_six :
    ForwardIdentityAtPair 7 6 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_7_0_6,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_seven_seven :
    ForwardIdentityAtPair 7 7 := by
  unfold ForwardIdentityAtPair
  intro sourceAB sourceABC targetBC targetABC
  fin_cases sourceAB <;>
    fin_cases sourceABC <;>
    fin_cases targetBC <;>
    fin_cases targetABC <;>
    funext e <;>
    fin_cases e <;>
    all_goals
    simp [rawX, realTForwardEntry, realTLeftPosition,
      realTRightPosition, Fin.ext_iff, Coeff.one, Coeff.zero,
      RMod.ConstructiveRouteFrame.frameEquiv_val,
      RMod.ConstructiveRouteFrame.collapsePositionNat,
      RMod.ConstructiveConnectorTable.forwardCoeff,
      RMod.ConstructiveConnectorTable.forwardCoeffNat,
      RMod.ConstructiveConnectorTable.sigmaNat,
      RMod.ConstructiveConnectorTable.forwardFlatNat,
      RMod.ConstructiveConnectorTable.reshapeCoeff,
      RMod.ConstructiveConnectorTable.forwardFlat_7_0_7,
      Superfusion.coeffGet, Superfusion.realRepDim]

private theorem forwardIdentityAt_seven : ForwardIdentityAt 7 := by
  intro c
  fin_cases c
  · exact forwardIdentityAt_seven_zero
  · exact forwardIdentityAt_seven_one
  · exact forwardIdentityAt_seven_two
  · exact forwardIdentityAt_seven_three
  · exact forwardIdentityAt_seven_four
  · exact forwardIdentityAt_seven_five
  · exact forwardIdentityAt_seven_six
  · exact forwardIdentityAt_seven_seven

/-! ## Public aggregate certificate -/

/-- All 64 label pairs of the frozen middle-unit connector, assembled from
the eight independently checked first-label slices. -/
theorem forwardEntry_middle_unit
    (a c : ZMod 8)
    (sourceAB : rawX.C.Index a 0)
    (sourceABC : rawX.C.Index (a + 0) c)
    (targetBC : rawX.C.Index 0 c)
    (targetABC : rawX.C.Index a (0 + c)) :
    realTForwardEntry a 0 c targetBC targetABC sourceAB sourceABC =
      if Associator.castIndex rawX (add_zero a) rfl sourceABC =
          Associator.castIndex rawX rfl (zero_add c) targetABC then
        Coeff.one (a + 0 + c)
      else Coeff.zero (a + 0 + c) := by
  fin_cases a
  · exact forwardIdentityAt_zero c sourceAB sourceABC targetBC targetABC
  · exact forwardIdentityAt_one c sourceAB sourceABC targetBC targetABC
  · exact forwardIdentityAt_two c sourceAB sourceABC targetBC targetABC
  · exact forwardIdentityAt_three c sourceAB sourceABC targetBC targetABC
  · exact forwardIdentityAt_four c sourceAB sourceABC targetBC targetABC
  · exact forwardIdentityAt_five c sourceAB sourceABC targetBC targetABC
  · exact forwardIdentityAt_six c sourceAB sourceABC targetBC targetABC
  · exact forwardIdentityAt_seven c sourceAB sourceABC targetBC targetABC

end RealMiddleUnitConnectorCertificate

end Superfusion.RMod.FromRawDCT
