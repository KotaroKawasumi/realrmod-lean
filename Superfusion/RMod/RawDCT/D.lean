import Mathlib.Data.Real.Basic
import Superfusion.RMod.RawDCT.Algebra

/-!
# Abstract coefficient families

`DData`, `DLaws`, and the completed `D` live together here.  This file has
no concrete real-gauge inhabitant.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT

/-- Computational data of an eight-label coefficient-algebra family. -/
structure DData where
  algebra : ZMod 8 → SuperAlgebraData ℝ

/-- Laws for the exact algebra data stored in `d`. -/
structure DLaws (d : DData) : Prop where
  algebra_laws : ∀ a, SuperAlgebraLaws (d.algebra a)

/-- A completed coefficient-algebra family. -/
structure D where
  data : DData
  laws : DLaws data

end Superfusion.RMod.RawDCT
