import Superfusion.GaugeChi.CoeffCheckerRect
import Superfusion.RMod.Constructive.ConnectorTableData
import Superfusion.RMod.Constructive.ConnectorTableRankLaws

/-!
# Raw forward semantic connector

This proof-only module realizes the frozen, unshifted forward connector table
in the native left and right frames of `realGauge`.  It contains no selected
inverse, regular-module shift, `ν`, `β`, or route normalization.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticConnector

open RMod.ConstructiveConnectorTable
open GaugeChi

/-! ## Native-frame coefficient realization -/

/-- The right native frame and the table's flat frame have the same size. -/
theorem rightTotal_eq_sigma : ∀ a b c : ZMod 8,
    (realGauge.gaugeSizeR a b c).1 + (realGauge.gaugeSizeR a b c).2 =
      sigma a b c := by
  simpa only [DivisionFusionGauge.gaugeSizeR, realGauge_size] using
    ConnectorTableRankLaws.rightTotal_eq_sigma

/-- The left native frame and the table's flat frame have the same size. -/
theorem leftTotal_eq_sigma : ∀ a b c : ZMod 8,
    (realGauge.gaugeSizeL a b c).1 + (realGauge.gaugeSizeL a b c).2 =
      sigma a b c := by
  simpa only [DivisionFusionGauge.gaugeSizeL, realGauge_size] using
    ConnectorTableRankLaws.leftTotal_eq_sigma

/-- Flatten the parity-split right route frame in the order used by the
frozen connector table. -/
noncomputable def rightFrameEquiv (a b c : ZMod 8) :
    (Fin (realGauge.gaugeSizeR a b c).1 ⊕
      Fin (realGauge.gaugeSizeR a b c).2) ≃ Fin (sigma a b c) :=
  Superfusion.frameEquiv (rightTotal_eq_sigma a b c)

/-- Flatten the parity-split left route frame in the order used by the
frozen connector table. -/
noncomputable def leftFrameEquiv (a b c : ZMod 8) :
    (Fin (realGauge.gaugeSizeL a b c).1 ⊕
      Fin (realGauge.gaugeSizeL a b c).2) ≃ Fin (sigma a b c) :=
  Superfusion.frameEquiv (leftTotal_eq_sigma a b c)

/-- The frozen raw connector in the native rectangular frame. -/
noncomputable def forwardMatrix (a b c : ZMod 8) :
    NativeT ℝ realGauge a b c :=
  matOfCoeff₂ (realRepBasis (a + (b + c))) fun r s e =>
    coeffOf (sigma a b c) (realRepDim (a + (b + c)).val)
      (forwardCoeff a b c) (rightFrameEquiv a b c r)
        (leftFrameEquiv a b c s) e

end RawSemanticConnector
end RModCoordinate
end Superfusion
