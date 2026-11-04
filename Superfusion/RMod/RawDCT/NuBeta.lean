import Superfusion.Cochain.RegularTrivialization
import Superfusion.RMod.RawDCT.PChi

/-!
# Raw obstruction trivialization cochains

This file contains the abstract `(ν, β)` data which trivializes a bundled
raw Gu--Wen obstruction.  It has no concrete real table or semantic connector
instance.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT

/-! ## Data, laws, and completed trivialization -/

/-- Computational cochains used to shift binary columns and rescale ternary
connectors. -/
structure NuBetaData where
  nu : RawDCTGroup → RawDCTGroup → ZMod 2
  beta : RawDCTGroup → RawDCTGroup → RawDCTGroup → ℝˣ

/-- The equations saying that `d` trivializes the exact cochains in `pchi`.

The parity equation removes the shifted connector degree.  The scalar
equation includes the regular quadratic sign introduced by that shift. -/
structure NuBetaLaws (x : RawDCTData) (hx : RawDCTLaws x)
    (pchi : PChiData) (hpchi : PChiLaws x hx pchi)
    (d : NuBetaData) : Prop where
  nu_normalized : Superfusion.Normalized₂ d.nu
  parity :
    ∀ a b c, Superfusion.d₂ d.nu a b c = rawParity x a b c
  pentagon :
    ∀ a b c e,
      pchi.chi a b c e *
          (Superfusion.sgn
            (Superfusion.regularQuadratic d.nu (rawParity x)
              a b c e) : ℝˣ) =
        Superfusion.dm₃ d.beta a b c e

/-- A completed `(ν, β)` trivialization of a bundled raw obstruction. -/
structure NuBeta (X : RawDCT) (P : PChi X) where
  data : NuBetaData
  laws : NuBetaLaws X.data X.laws P.data P.laws data

/-! ## Adapter from the existing cochain structure -/

/-- Retain the computational fields of an existing regular
trivialization. -/
def nuBetaDataOfRegular {p : ParityCochain} {chi : ScalarCochain}
    (t : Superfusion.RegularTrivialization p chi) : NuBetaData where
  nu := t.ν
  beta := t.β

/-- The proof fields of a regular trivialization are exactly the raw
`NuBetaLaws` equations. -/
def nuBetaLawsOfRegular (x : RawDCTData) (hx : RawDCTLaws x)
    (pchi : PChiData) (hpchi : PChiLaws x hx pchi)
    (t : Superfusion.RegularTrivialization (rawParity x) pchi.chi) :
    NuBetaLaws x hx pchi hpchi (nuBetaDataOfRegular t) where
  nu_normalized := t.ν_normalized
  parity := t.parity
  pentagon := t.pentagon

/-- Bundle an existing regular trivialization without changing either
cochain. -/
def nuBetaOfRegular (X : RawDCT) (P : PChi X)
    (t : Superfusion.RegularTrivialization (rawParity X.data) P.data.chi) :
    NuBeta X P where
  data := nuBetaDataOfRegular t
  laws := nuBetaLawsOfRegular X.data X.laws P.data P.laws t

end Superfusion.RMod.RawDCT
