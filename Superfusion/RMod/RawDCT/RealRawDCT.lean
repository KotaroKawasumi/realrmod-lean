import Superfusion.RMod.RawDCT.RawDCT
import Superfusion.RMod.RawDCT.RealT

/-!
# The computable real raw DCT bundle

This file assembles the separately constructed real `D`, `C`, and `T`
layers.  No table is recomputed here: the data and proofs are reused from
their dedicated instance files.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT

/-! ## Executable real data -/

/-- The complete executable raw DCT data over `ℝ` and `ZMod 8`. -/
def realRawDCTData : RawDCTData where
  D := realDData
  C := realCData
  T := realTData

/-! ## Laws of the exact real data -/

/-- The already established `D`, `C`, and `T` laws attached to the exact
records in `realRawDCTData`. -/
theorem realRawDCTLaws : RawDCTLaws realRawDCTData where
  D := realDLaws
  C := realCLaws
  T := realTLaws

/-! ## Completed real bundle -/

/-- The completed computable raw real DCT package. -/
def realRawDCT : RawDCT where
  data := realRawDCTData
  laws := realRawDCTLaws

/-! ## Nontrivial checks through the completed bundle -/

/-- The completed bundle retains a genuinely odd raw connector. -/
theorem realRawDCT_example_parity :
    realRawDCT.data.T.parity 1 1 4 = 1 :=
  rfl

example : realRawDCT.data.T.parity 1 1 4 = 1 :=
  realRawDCT_example_parity

/-- The completed bundle exposes the certified connector inverse on a
rectangular route triple. -/
theorem realRawDCT_example_inv_hom
    (m : realRawDCT.data.T.LeftCarrier 1 4 4) :
    realRawDCT.data.T.inv 1 4 4 (realRawDCT.data.T.hom 1 4 4 m) = m :=
  realRawDCT.laws.T.inv_hom_id 1 4 4 m

example (m : realRawDCT.data.T.LeftCarrier 1 4 4) :
    realRawDCT.data.T.inv 1 4 4 (realRawDCT.data.T.hom 1 4 4 m) = m :=
  realRawDCT_example_inv_hom m

end Superfusion.RMod.RawDCT
