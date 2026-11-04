import Superfusion.Cochain.Cup
import Superfusion.RMod.RawDCT.RawDCT

/-!
# Raw Gu--Wen obstruction cochains

This file contains only the abstract cochain package attached after the
`D → C → T` layers.  Its parity cochain is read directly from the stored raw
connector.  The scalar slot is where a later constructor stores the
fourfold defect derived from that connector.

The abstract structure is independent of a particular semantic gauge, so
its laws record the Gu--Wen cochain equations.  The constructor in
`PChiOfConnector.lean` derives the scalar from a realization of the stored
raw `T` and proves the corresponding top-versus-bottom route equation.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT

/-! ## Cochains determined by raw labels -/

/-- Multiplicative presentation of the additive label group of a raw DCT. -/
abbrev RawDCTGroup : Type := Multiplicative (ZMod 8)

/-- Degree-three parity cochains on the raw label group. -/
abbrev ParityCochain : Type :=
  RawDCTGroup → RawDCTGroup → RawDCTGroup → ZMod 2

/-- Degree-four real-unit scalar cochains on the raw label group. -/
abbrev ScalarCochain : Type :=
  RawDCTGroup → RawDCTGroup → RawDCTGroup → RawDCTGroup → ℝˣ

/-- The parity cochain is part of the raw `T` data and is not stored again in
`PChiData`. -/
def rawParity (x : RawDCTData) : ParityCochain :=
  fun a b c => x.T.parity a.toAdd b.toAdd c.toAdd

/-! ## Data, laws, and completed obstruction -/

/-- Scalar cochain data of a raw Gu--Wen obstruction. -/
structure PChiData where
  chi : ScalarCochain

/-- The cohomological laws of the exact data in `d`.

The first equation says that the parity already stored in `x.T` is a
three-cocycle.  The second is the Gu--Wen supercocycle equation for the stored
scalar table. -/
structure PChiLaws (x : RawDCTData) (hx : RawDCTLaws x)
    (d : PChiData) : Prop where
  p_cocycle :
    ∀ a b c e, Superfusion.d₃ (rawParity x) a b c e = 0
  chi_supercocycle :
    ∀ a b c e f,
      Superfusion.dm₄ d.chi a b c e f =
        (Superfusion.sgn
          (Superfusion.cupOne₃₃ (rawParity x) (rawParity x)
            a b c e f) : ℝˣ)

/-- A raw DCT together with a scalar obstruction and laws about that exact
cochain data. -/
structure PChi (X : RawDCT) where
  data : PChiData
  laws : PChiLaws X.data X.laws data

end Superfusion.RMod.RawDCT
