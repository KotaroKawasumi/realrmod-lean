import Superfusion.RMod.FromRawDCT.Candidate
import Superfusion.RMod.RawDCT.RealComputableShift

/-!
# Concrete candidate data from the computably shifted real raw DCT

This file contains only the concrete executable instance layer.  The unit
rows are the unique zero-indexed rows of the shifted real unit faces, and
the candidate is obtained from `realComputableShiftedRawDCT.data` itself.
No old semantic `RModCarrier`, `realTriv`, `nu`, or `beta` is reapplied.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open RawDCT

/-! ## Concrete unit rows -/

/-- The zero-indexed rows on the two real unit faces. -/
def realUnitRowsData : UnitRowsData
    realComputableShiftedRawDCT.data.D
    realComputableShiftedRawDCT.data.C where
  left := fun a => ⟨0, by
    change 0 < (realSize 0 a).1 + (realSize 0 a).2
    have hs : realSize 0 a = (1, 0) := rfl
    rw [hs]
    omega⟩
  right := fun a => ⟨0, by
    change 0 < (realSize a 0).1 + (realSize a 0).2
    have hs : realSize a 0 = (1, 0) := by
      fin_cases a <;> rfl
    rw [hs]
    omega⟩

/-- Uniqueness and evenness of those exact shifted rows. -/
def realUnitRowsLaws : UnitRowsLaws
    realComputableShiftedRawDCT.data.D
    realComputableShiftedRawDCT.data.C realUnitRowsData where
  left_unique := by
    intro a r
    fin_cases a <;> fin_cases r <;> rfl
  right_unique := by
    intro a r
    fin_cases a <;> fin_cases r <;> rfl
  left_even := by
    intro a
    fin_cases a <;> rfl
  right_even := by
    intro a
    fin_cases a <;> rfl

/-- Completed real unit-row package. -/
def realUnitRows : UnitRows
    { data := realComputableShiftedRawDCT.data.D
      laws := realComputableShiftedRawDCT.laws.D }
    { data := realComputableShiftedRawDCT.data.C
      laws := realComputableShiftedRawDCT.laws.C } where
  data := realUnitRowsData
  laws := realUnitRowsLaws

/-! ## Concrete proof-free candidate -/

/-- The computable finite coordinate candidate formed directly from the
shifted real `D`, `C`, and `T`. -/
def realCandidateData : Superfusion.CandidateData :=
  Candidate.data realComputableShiftedRawDCT.data realUnitRowsData

/-! ## Closed nontrivial evaluations -/

/-- The shifted tensor remembers the nonzero binary regrading at `(1,1)`. -/
example :
    Atom.shift
      ((Tensor.obj realComputableShiftedRawDCT.data.D
          realComputableShiftedRawDCT.data.C
          (Obj.singleton (1, 0)) (Obj.singleton (1, 0))).atom
        ⟨0, by change 0 < 1; omega⟩) = 1 :=
  rfl

/-- The `(1,3)` tensor has two distinct stored fusion rows. -/
example :
    (Tensor.obj realComputableShiftedRawDCT.data.D
      realComputableShiftedRawDCT.data.C
      (Obj.singleton (1, 0)) (Obj.singleton (3, 0))).size = 2 :=
  rfl

end Superfusion.RMod.FromRawDCT
