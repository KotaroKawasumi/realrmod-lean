import Superfusion.RMod.RawDCT.T

/-!
# Abstract raw DCT bundles

This file assembles the abstract `D → C → T` tower.  It contains no
concrete coefficient tables or real-gauge instance.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT

/-! ## Executable data -/

/-- The computational data of a raw DCT package, with each layer depending
on the data of the preceding layers. -/
structure RawDCTData where
  D : DData
  C : CData D
  T : TData D C

/-! ## Laws of the exact stored data -/

/-- Laws for the three exact records stored in `x`. -/
structure RawDCTLaws (x : RawDCTData) : Prop where
  D : DLaws x.D
  C : CLaws x.D D x.C
  T : TLaws x.D D x.C C x.T

/-! ## Completed structure -/

/-- A completed raw DCT package, bundling executable data with laws about
that same data. -/
structure RawDCT where
  data : RawDCTData
  laws : RawDCTLaws data

end Superfusion.RMod.RawDCT
