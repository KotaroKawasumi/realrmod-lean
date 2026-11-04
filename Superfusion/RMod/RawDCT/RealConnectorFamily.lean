import Superfusion.GaugeChi.ConnectorFamily
import Superfusion.RMod.Constructive.ConnectorTableRouteInverseLaws
import Superfusion.RMod.Constructive.RawSemanticConnectorMem

/-!
# Semantic family of the frozen raw connector

The raw `TData` and the semantic matrix below have the same source of truth:
`ConstructiveConnectorTable.forwardCoeff`.  This file only packages that
already checked ternary table as a `ConnectorFamily`.  In particular, it
does not form or evaluate either fourfold pentagon route.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT

open GaugeChi
open RMod.ConstructiveConnectorTable
open RModCoordinate

/-! ## Nonvanishing from the saved inverse certificate -/

/-- The common flat route rank is positive.  This is a structural
consequence of the nonzero gauge sizes, not a new finite-table check. -/
theorem realRawSigma_pos (a b c : ZMod 8) :
    0 < sigma a b c := by
  apply Nat.pos_of_ne_zero
  rw [← RawSemanticConnector.leftTotal_eq_sigma a b c]
  exact realGauge.gaugeSizeL_ne_zero a b c

/-- The integer coefficient function of the saved forward table is nonzero.
If it vanished, the already certified forward--inverse product would be
both zero and the nonzero scalar identity. -/
theorem realRawForwardCoeff_ne_zero (a b c : ZMod 8) :
    coeffOf (sigma a b c) (realRepDim (a + b + c).val)
        (RMod.ConstructiveConnectorTable.forwardCoeff a b c) ≠ 0 := by
  intro hzero
  let r : Fin (sigma a b c) := ⟨0, realRawSigma_pos a b c⟩
  let e : Fin (realRepDim (a + b + c).val) :=
    ⟨0, realRepDim_pos (a + b + c).val⟩
  have h := RModCoordinate.ConnectorTableLaws.rawForwardInverseCoeffAtTotalLabel
    a b c r r e
  rw [hzero] at h
  have hscale : (inverseScale a b c : ℤ) ≠ 0 := by
    exact_mod_cast inverseScale_ne_zero a b c
  have : (0 : ℤ) = inverseScale a b c := by
    simpa [convCoeff, r, e] using h
  exact hscale this.symm

/-- The native semantic matrix is nonzero.  Coefficient uniqueness reduces
this directly to `realRawForwardCoeff_ne_zero`; no connector or pentagon is
recomputed. -/
theorem realRawForwardMatrix_ne_zero (a b c : ZMod 8) :
    RawSemanticConnector.forwardMatrix a b c ≠ 0 := by
  intro hzero
  let x := fun
      (r : Fin (realGauge.gaugeSizeR a b c).1 ⊕
        Fin (realGauge.gaugeSizeR a b c).2)
      (s : Fin (realGauge.gaugeSizeL a b c).1 ⊕
        Fin (realGauge.gaugeSizeL a b c).2)
      (e : Fin (realRepDim (a + (b + c)).val)) =>
    coeffOf (sigma a b c) (realRepDim (a + (b + c)).val)
      (RMod.ConstructiveConnectorTable.forwardCoeff a b c)
      (RawSemanticConnector.rightFrameEquiv a b c r)
      (RawSemanticConnector.leftFrameEquiv a b c s) e
  have hzeroMatrix :
      (0 : NativeT ℝ realGauge a b c) =
        matOfCoeff₂ (realRepBasis (a + (b + c)))
          (fun _ _ _ => (0 : ℤ)) := by
    ext r s
    simp [matOfCoeff₂_apply]
    rfl
  have hx : x = fun _ _ _ => (0 : ℤ) := by
    apply matOfCoeff₂_injective (realRepBasis (a + (b + c)))
    exact hzero.trans hzeroMatrix
  have hflat :
      coeffOf (sigma a b c) (realRepDim (a + (b + c)).val)
          (RMod.ConstructiveConnectorTable.forwardCoeff a b c) = 0 := by
    funext r s e
    have h := congrFun (congrFun (congrFun hx
      ((RawSemanticConnector.rightFrameEquiv a b c).symm r))
      ((RawSemanticConnector.leftFrameEquiv a b c).symm s)) e
    simpa [x] using h
  apply realRawForwardCoeff_ne_zero a b c
  rw [congrArg ZMod.val (_root_.add_assoc a b c)]
  exact hflat

/-! ## Completed semantic connector family -/

/-- The semantic realization of the frozen raw forward table.  Its
membership proof is the existing 512-triple certificate rollout, while its
nonvanishing is obtained above from the stored two-sided inverse
certificate. -/
noncomputable def realRawConnectorFamily : ConnectorFamily ℝ realGauge where
  T a b c := gtOfTNative ℝ realGauge a b c
    (RawSemanticConnector.forwardMatrix a b c)
  parity := RModCoordinate.RawSemanticSkeletalData.parity
  mem := RModCoordinate.RawSemanticSkeletalData.forward_mem
  ne_zero a b c := gtOfTNative_ne_zero ℝ realGauge a b c
    (realRawForwardMatrix_ne_zero a b c)

end Superfusion.RMod.RawDCT
