/-
Superfusion / RMod / Constructive / ConnectorTableRankLaws

Rank identities shared by the raw forward connector and its inverse.  This
module depends only on the frozen fusion-size and connector-size data, so
consumers of the identities do not acquire either semantic connector laws or
inverse certificates.
-/
import Superfusion.RMod.Constructive.ConnectorTableData
import Superfusion.RMod.Constructive.FusionTableData

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace ConnectorTableRankLaws

open RMod.ConstructiveConnectorTable

/-! ## Equality of route ranks and the frozen connector rank

The two parenthesizations split their fusion-row pairs by total parity.  The
following closed finite proofs certify that both parity-split totals are the
single table rank `sigma`.  They are kept here once and reused by both the
forward semantic realization and the inverse route reindexing.
-/

/-- The left-associated fusion-row pair has the frozen connector rank. -/
theorem leftTotal_eq_sigma : ∀ a b c : ZMod 8,
    ((realSize a b).1 * (realSize (a + b) c).1 +
        (realSize a b).2 * (realSize (a + b) c).2) +
      ((realSize a b).1 * (realSize (a + b) c).2 +
        (realSize a b).2 * (realSize (a + b) c).1) =
      sigma a b c := by
  decide +kernel

/-- The right-associated fusion-row pair has the frozen connector rank. -/
theorem rightTotal_eq_sigma : ∀ a b c : ZMod 8,
    ((realSize b c).1 * (realSize a (b + c)).1 +
        (realSize b c).2 * (realSize a (b + c)).2) +
      ((realSize b c).1 * (realSize a (b + c)).2 +
        (realSize b c).2 * (realSize a (b + c)).1) =
      sigma a b c := by
  intro a b c
  calc
    ((realSize b c).1 * (realSize a (b + c)).1 +
          (realSize b c).2 * (realSize a (b + c)).2) +
        ((realSize b c).1 * (realSize a (b + c)).2 +
          (realSize b c).2 * (realSize a (b + c)).1) =
      ((realSize a b).1 * (realSize (a + b) c).1 +
          (realSize a b).2 * (realSize (a + b) c).2) +
        ((realSize a b).1 * (realSize (a + b) c).2 +
          (realSize a b).2 * (realSize (a + b) c).1) := by
      simpa only [DivisionFusionGauge.gaugeSizeR,
        DivisionFusionGauge.gaugeSizeL, realGauge_size] using
        (sizeRigidity_total (realGauge.frameAlign a b c))
    _ = sigma a b c := leftTotal_eq_sigma a b c

end ConnectorTableRankLaws
end RModCoordinate
end Superfusion
