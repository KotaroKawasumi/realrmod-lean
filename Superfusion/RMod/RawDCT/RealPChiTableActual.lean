import Superfusion.RMod.RawDCT.PChiSoundness
import Superfusion.RMod.RawDCT.RealNuBetaTable
import Superfusion.RMod.RawDCT.RealPChi
import Superfusion.RMod.RawDCT.RealPChiCertificate
import Superfusion.RMod.RawDCT.RealPChiRouteBottom
import Superfusion.RMod.RawDCT.RealPChiRouteTop

/-!
# Actuality of the computable real obstruction table

This concrete instance file joins three independently checked ingredients:

* the executable dyadic table `realPChiTableData`;
* an exact source/target witness for every ordered quadruple; and
* the semantic coordinate bridges for the actual top and bottom routes of
  `realRawDCT.T`.

The resulting soundness certificate identifies the executable table with
the semantic obstruction `realPChi`.  The proof witness uses semantic basis
coordinates and is therefore noncomputable, but the identified `(p, chi)`
data remain exactly the original computable dyadic table.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT

open GaugeChi
open RealPChiKernel

/-! ## Coordinate witnesses for the actual route -/

/-- For each quadruple, use the checked flat source-zero generator and its
checked nonzero bottom-route target coordinate.

This is proof-only observation data.  It does not replace or modify the
computable scalar table. -/
noncomputable def realPChiTableSoundnessData :
    PChiSoundnessData realGauge where
  source := fun a b c d =>
    let h := RealPChiCertificate.exactWitness a b c d
    RealPChiRouteBridge.semanticSource a b c d h.source
  observe := fun a b c d =>
    let h := RealPChiCertificate.exactWitness a b c d
    RealPChiRouteBridge.semanticObserve a b c d h.target

/-! ## Exact soundness laws -/

/-- The selected bottom coordinate is nonzero, and the selected top
coordinate is the frozen dyadic table value times that bottom coordinate.

Both route coordinates are coordinates of the actual semantic connector
realizing the stored raw `T`; the kernel equality is checked in exact
rational arithmetic before being cast to `ℝ`. -/
theorem realPChiTableSoundnessLaws :
    PChiSoundnessLaws realGauge realConnectorRealization
      realPChiTableData realPChiTableSoundnessData := by
  constructor
  · intro a b c d
    let h := RealPChiCertificate.exactWitness a b c d
    change RealPChiRouteBridge.semanticObserve a b c d h.target
        (famBot ℝ realGauge realConnectorRealization.toConnectorFamily
          a b c d
          (RealPChiRouteBridge.semanticSource a b c d h.source)) ≠ 0
    rw [RealPChiRouteBottom.semanticObserve_famBot]
    exact_mod_cast h.bottom_ne_zero
  · intro a b c d
    let h := RealPChiCertificate.exactWitness a b c d
    change RealPChiRouteBridge.semanticObserve a b c d h.target
        (famTop ℝ realGauge realConnectorRealization.toConnectorFamily
          a b c d
          (RealPChiRouteBridge.semanticSource a b c d h.source)) =
      ((realPChiTableData.chi
          (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
          (Multiplicative.ofAdd c) (Multiplicative.ofAdd d) : ℝˣ) : ℝ) *
        RealPChiRouteBridge.semanticObserve a b c d h.target
          (famBot ℝ realGauge realConnectorRealization.toConnectorFamily
            a b c d
            (RealPChiRouteBridge.semanticSource a b c d h.source))
    rw [show
      RealPChiRouteBridge.semanticObserve a b c d h.target
          (famTop ℝ realGauge
            realConnectorRealization.toConnectorFamily a b c d
            (RealPChiRouteBridge.semanticSource a b c d h.source)) =
        ((topCoeff a b c d h.source h.target : ℤ) : ℝ) by
          simpa [ConnectorRealization.toConnectorFamily,
            ConnectorRealization.toConnectorFamilyOfData,
            realConnectorRealization, realConnectorRealizationData] using
            RealPChiRouteTop.semanticObserve_famTop
              a b c d h.source h.target,
      RealPChiRouteBottom.semanticObserve_famBot]
    rw [show
      ((realPChiTableData.chi
          (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
          (Multiplicative.ofAdd c) (Multiplicative.ofAdd d) : ℝˣ) : ℝ) =
        ((RealPChiCertificate.tableValue a b c d : ℚ) : ℝ) by rfl]
    exact_mod_cast h.top_eq

/-! ## Completed soundness and pointwise actuality -/

/-- Observation data bundled with laws for the exact executable table. -/
noncomputable def realPChiTableSoundness :
    PChiSoundness realGauge realConnectorRealization realPChiTableData where
  data := realPChiTableSoundnessData
  laws := realPChiTableSoundnessLaws

/-- The executable table gives the actual top-versus-bottom scalar for every
ordered quadruple. -/
theorem realPChiTable_isSound :
    IsPChiSound realConnectorRealization realPChiTableData :=
  realPChiTableSoundness.isSound

/-- The executable dyadic cochain is exactly the cochain derived from the
actual connector realized by `realRawDCT.T`. -/
theorem realPChiTableData_eq_realPChiData :
    realPChiTableData = realPChiData :=
  eq_of_isPChiSound realPChiTable_isSound
    (pChiDataOfConnectorRealization_isSound realConnectorRealization)

/-- Equality of data determines equality of completed `PChi` bundles because
all remaining fields are laws in `Prop`. -/
theorem realPChiTableCertificate_eq_realPChi :
    realPChiTableCertificate = realPChi := by
  have hdata : realPChiTableCertificate.data = realPChi.data :=
    realPChiTableData_eq_realPChiData
  have data_injective : ∀ (x y : PChi realRawDCT),
      x.data = y.data → x = y := by
    intro x y h
    cases x with
    | mk xData xLaws =>
        cases y with
        | mk yData yLaws =>
            cases h
            rfl
  exact data_injective _ _ hdata

/-! ## Computable presentation of the actual obstruction -/

/-- A computable presentation of the actual obstruction.  Its fields reduce
to the frozen dyadic table; actuality is supplied separately by the theorem
above rather than by changing its computational content. -/
def realComputablePChi : PChi realRawDCT :=
  realPChiTableCertificate

/-- The computable presentation is the actual semantic obstruction. -/
theorem realComputablePChi_eq_realPChi :
    realComputablePChi = realPChi :=
  realPChiTableCertificate_eq_realPChi

/-! ## Concrete actual-route checks -/

/-- At the nontrivial all-four sector, the executable scalar is the actual
top-to-bottom route scalar. -/
example :
    famTop ℝ realGauge realConnectorRealization.toConnectorFamily 4 4 4 4 =
      ((realComputablePChi.data.chi
        (Multiplicative.ofAdd 4) (Multiplicative.ofAdd 4)
        (Multiplicative.ofAdd 4) (Multiplicative.ofAdd 4) : ℝˣ) : ℝ) •
        famBot ℝ realGauge realConnectorRealization.toConnectorFamily
          4 4 4 4 :=
  realPChiTable_isSound 4 4 4 4

/-- A second nonidentity quadruple exposes the same actual-route guarantee,
independently of the all-four calculation. -/
example :
    famTop ℝ realGauge realConnectorRealization.toConnectorFamily 1 2 3 4 =
      ((realComputablePChi.data.chi
        (Multiplicative.ofAdd 1) (Multiplicative.ofAdd 2)
        (Multiplicative.ofAdd 3) (Multiplicative.ofAdd 4) : ℝˣ) : ℝ) •
        famBot ℝ realGauge realConnectorRealization.toConnectorFamily
          1 2 3 4 :=
  realPChiTable_isSound 1 2 3 4

end Superfusion.RMod.RawDCT
