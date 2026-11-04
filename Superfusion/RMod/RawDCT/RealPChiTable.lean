import Superfusion.Cochain.RegularTrivializationTransport
import Superfusion.GaugeChi.HchiProto
import Superfusion.GaugeChi.RealGaugeTrivializationTable
import Superfusion.RMod.RawDCT.DyadicReal
import Superfusion.RMod.RawDCT.PChi
import Superfusion.RMod.RawDCT.RealRawDCT

/-!
# Computable real obstruction-table certificate

This file packages the frozen Lean-frame `(p, chi)` table and its already
proved cochain equations.  It deliberately does not call this table
`realPChi`: that name is reserved for the actual fourfold defect derived
from `realRawDCT` in `RealPChi.lean`.

The table remains useful computational certificate data.  Identifying it
pointwise with the actual raw connector defect would require an additional
semantic bridge theorem; no such identification is asserted here.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT

open GaugeChi

/-! ## Computable table data -/

/-- The frozen scalar table, mapped to real units without real inversion. -/
def realPChiTableData : PChiData where
  chi := fun a b c d =>
    dyadicRealHom (realLeanChiTable a b c d)

/-- The parity stored in the raw connector is definitionally the frozen
Lean-frame parity table. -/
theorem realRawParity_eq_realLeanParityTable :
    rawParity realRawDCTData = realLeanParityTable := by
  funext a b c
  exact realT_parity_eq_realLeanParityTable a.toAdd b.toAdd c.toAdd

/-! ## Existing table laws -/

/-- The saved dyadic trivialization mapped through the computable real-unit
realization. -/
def realLeanTableTrivializationReal :
    Superfusion.RegularTrivialization
      realLeanParityTable realPChiTableData.chi :=
  (realLeanTableTrivialization.map dyadicRealHom dyadicRealHom_sign).copy
    realLeanParityTable realPChiTableData.chi
    (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)

/-- The same table trivialization with parity written as the parity stored in
the raw `T`.  This is a cochain-table statement, not an actuality claim. -/
def realRawTableTrivialization :
    Superfusion.RegularTrivialization
      (rawParity realRawDCTData) realPChiTableData.chi :=
  realLeanTableTrivializationReal.copy
    (rawParity realRawDCTData) realPChiTableData.chi
    (fun a b c => congrFun (congrFun (congrFun
      realRawParity_eq_realLeanParityTable a) b) c)
    (fun _ _ _ _ => rfl)

/-- Cohomological laws of the frozen table.  The scalar equation is obtained
by mapping the already-proved dyadic theorem; no finite calculation is
introduced here. -/
theorem realPChiTableLaws :
    PChiLaws realRawDCTData realRawDCTLaws realPChiTableData := by
  refine {
    p_cocycle := realRawTableTrivialization.p_isCocycle
    chi_supercocycle := ?_ }
  intro a b c d e
  have h := congrArg dyadicRealHom
    (dm₄_realLeanChiTable a b c d e)
  rw [map_dm₄, map_sgn dyadicRealHom dyadicRealHom_sign] at h
  rw [realRawParity_eq_realLeanParityTable]
  exact h

/-! ## Closed table evaluations -/

/-- The raw parity table is genuinely nonzero. -/
example :
    rawParity realRawDCT.data
      (Multiplicative.ofAdd 1) (Multiplicative.ofAdd 1)
      (Multiplicative.ofAdd 4) = 1 :=
  rfl

/-- The frozen scalar certificate has its normalized value at the identity
quadruple. -/
example :
    ((realPChiTableData.chi
      (Multiplicative.ofAdd 0) (Multiplicative.ofAdd 0)
      (Multiplicative.ofAdd 0) (Multiplicative.ofAdd 0) : ℝˣ) : ℝ) = 1 := by
  change ((dyadicRatValue
    (realLeanChiTable
      (Multiplicative.ofAdd 0) (Multiplicative.ofAdd 0)
      (Multiplicative.ofAdd 0) (Multiplicative.ofAdd 0)) : ℚ) : ℝ) = 1
  norm_num [realLeanChiTable, chiLeanSignBits, chiLeanExpNibbles,
    bitAt, nibbleAt, idx4, ix]

end Superfusion.RMod.RawDCT
