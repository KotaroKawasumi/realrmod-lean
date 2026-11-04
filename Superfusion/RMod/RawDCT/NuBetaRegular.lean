import Superfusion.RMod.RawDCT.NuBeta

/-!
# Raw trivialization as a regular trivialization

This file contains the abstract reverse adapter from the separated raw
`NuBetaData`/`NuBetaLaws` presentation to the existing cochain-level
`RegularTrivialization`.  It contains no concrete real instance.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT

/-! ## Reverse adapter for separated data and laws -/

/-- Repackage the exact computational cochains in `n`, using the laws about
that same `n`, as the existing cochain-level regular trivialization. -/
def regularTrivializationOfNuBetaData
    (x : RawDCTData) (hx : RawDCTLaws x)
    (pchi : PChiData) (hpchi : PChiLaws x hx pchi)
    (n : NuBetaData) (hn : NuBetaLaws x hx pchi hpchi n) :
    Superfusion.RegularTrivialization (rawParity x) pchi.chi where
  ν := n.nu
  β := n.beta
  ν_normalized := hn.nu_normalized
  parity := hn.parity
  pentagon := hn.pentagon

/-- The adapter preserves the parity-shift cochain definitionally. -/
@[simp] theorem regularTrivializationOfNuBetaData_nu
    (x : RawDCTData) (hx : RawDCTLaws x)
    (pchi : PChiData) (hpchi : PChiLaws x hx pchi)
    (n : NuBetaData) (hn : NuBetaLaws x hx pchi hpchi n) :
    (regularTrivializationOfNuBetaData x hx pchi hpchi n hn).ν = n.nu :=
  rfl

/-- The adapter preserves the connector-rescaling cochain definitionally. -/
@[simp] theorem regularTrivializationOfNuBetaData_beta
    (x : RawDCTData) (hx : RawDCTLaws x)
    (pchi : PChiData) (hpchi : PChiLaws x hx pchi)
    (n : NuBetaData) (hn : NuBetaLaws x hx pchi hpchi n) :
    (regularTrivializationOfNuBetaData x hx pchi hpchi n hn).β = n.beta :=
  rfl

/-! ## Reverse adapter for completed packages -/

/-- Forget only the project-local outer bundle of a completed `NuBeta`.
The stored cochains themselves remain executable fields of the result. -/
def regularTrivializationOfNuBeta (X : RawDCT) (P : PChi X)
    (N : NuBeta X P) :
    Superfusion.RegularTrivialization (rawParity X.data) P.data.chi :=
  regularTrivializationOfNuBetaData
    X.data X.laws P.data P.laws N.data N.laws

/-! ## Round trips through the existing adapter -/

/-- Passing separated raw data through the reverse adapter and back loses no
computational information. -/
@[simp] theorem nuBetaDataOfRegular_reverse
    (x : RawDCTData) (hx : RawDCTLaws x)
    (pchi : PChiData) (hpchi : PChiLaws x hx pchi)
    (n : NuBetaData) (hn : NuBetaLaws x hx pchi hpchi n) :
    nuBetaDataOfRegular
      (regularTrivializationOfNuBetaData x hx pchi hpchi n hn) = n :=
  rfl

/-- Repackaging an existing regular trivialization into separated raw form and
then reversing that packaging returns the original cochain structure. -/
@[simp] theorem regularTrivialization_reverse_nuBetaDataOfRegular
    (x : RawDCTData) (hx : RawDCTLaws x)
    (pchi : PChiData) (hpchi : PChiLaws x hx pchi)
    (t : Superfusion.RegularTrivialization (rawParity x) pchi.chi) :
    regularTrivializationOfNuBetaData x hx pchi hpchi
      (nuBetaDataOfRegular t)
      (nuBetaLawsOfRegular x hx pchi hpchi t) = t := by
  cases t
  rfl

end Superfusion.RMod.RawDCT
