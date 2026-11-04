import Superfusion.RMod.RawDCT.PChiOfConnector
import Superfusion.RMod.RawDCT.RealConnectorRealization

/-!
# The actual obstruction of the computable real raw DCT

`realPChi` is derived from `realRawDCT`, not assigned an independent scalar
table.  The realization theorem identifies the stored executable `T.hom`
with the explicit semantic connector family.  The generic constructor then
uses the existing fourfold route theorem to obtain its actual pentagon
defect.

The semantic connector ratio used by the existing theorem is chosen from a
one-dimensional intertwiner line, so this proof-level realization of the
actual defect is noncomputable.  The separate file `RealPChiTable.lean`
retains the executable frozen table certificate without identifying it with
this actual defect.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT

open GaugeChi

/-! ## Actual data, laws, and completed obstruction -/

/-- The actual fourfold obstruction data of `realRawDCT`. -/
noncomputable def realPChiData : PChiData :=
  pChiDataOfConnectorRealization realConnectorRealization

/-- The Gu--Wen laws inherited from the actual connector-family defect. -/
theorem realPChiLaws :
    PChiLaws realRawDCTData realRawDCTLaws realPChiData :=
  pChiLawsOfConnectorRealization realConnectorRealization

/-- The actual `(p, chi)` derived from the raw real DCT. -/
noncomputable def realPChi : PChi realRawDCT :=
  pChiOfConnectorRealization realConnectorRealization

/-! ## Explicit actuality statements -/

/-- The value of `realPChi.chi` is the scalar selected by the existing
fourfold route comparison for the semantic realization of `realRawDCT.T`. -/
theorem realPChi_chi_val (a b c d : RawDCTGroup) :
    (((realPChi.data.chi a b c d : ℝˣ) : ℝ)) =
      chiOfFamily ℝ realGauge realConnectorRealization.toConnectorFamily
        a.toAdd b.toAdd c.toAdd d.toAdd :=
  pChiDataOfConnectorRealization_chi_val
    realConnectorRealization a b c d

/-- The top route of the connector realized by the stored raw `T` differs
from the bottom route by exactly `realPChi.chi`. -/
theorem realPChi_actual (a b c d : ZMod 8) :
    famTop ℝ realGauge realConnectorRealization.toConnectorFamily a b c d =
      ((realPChi.data.chi
        (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
        (Multiplicative.ofAdd c) (Multiplicative.ofAdd d) : ℝˣ) : ℝ) •
        famBot ℝ realGauge realConnectorRealization.toConnectorFamily
          a b c d :=
  pChiDataOfConnectorRealization_actual
    realConnectorRealization a b c d

/-! ## Concrete nontrivial checks -/

/-- The parity component derived from the raw connector is genuinely odd. -/
example :
    rawParity realRawDCT.data
      (Multiplicative.ofAdd 1) (Multiplicative.ofAdd 1)
      (Multiplicative.ofAdd 4) = 1 :=
  rfl

/-- At a nontrivial quadruple the completed object exposes the actual
top-versus-bottom route equation, rather than an independently assigned
table value. -/
example :
    famTop ℝ realGauge realConnectorRealization.toConnectorFamily 4 4 4 4 =
      ((realPChi.data.chi
        (Multiplicative.ofAdd 4) (Multiplicative.ofAdd 4)
        (Multiplicative.ofAdd 4) (Multiplicative.ofAdd 4) : ℝˣ) : ℝ) •
        famBot ℝ realGauge realConnectorRealization.toConnectorFamily
          4 4 4 4 :=
  realPChi_actual 4 4 4 4

end Superfusion.RMod.RawDCT
