import Superfusion.RMod.RawDCT.NuBeta
import Superfusion.RMod.RawDCT.RealPChiTable

/-!
# Computable real `(nu, beta)` table certificate

The frozen `(chi, nu, beta)` tables and their already-proved cochain laws are
kept here as an executable certificate package.  These declarations are not
named `realPChi` or `realNuBeta`: those names in the neighboring files denote
the actual obstruction of the connector realized by `realRawDCT.T` and its
transported trivialization.

No pointwise equality between the frozen scalar table and the actual
fourfold connector defect is asserted in this file.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT

open GaugeChi

/-! ## Completed computable table packages -/

/-- The frozen `(p, chi)` cochain certificate, bundled only with its
cohomological laws. -/
def realPChiTableCertificate : PChi realRawDCT where
  data := realPChiTableData
  laws := realPChiTableLaws

/-- The executable shift and rescaling tables. -/
def realNuBetaTableData : NuBetaData :=
  nuBetaDataOfRegular realRawTableTrivialization

/-- The saved table theorem supplies all `(nu, beta)` cochain laws. -/
def realNuBetaTableLaws :
    NuBetaLaws realRawDCTData realRawDCTLaws
      realPChiTableData realPChiTableLaws realNuBetaTableData :=
  nuBetaLawsOfRegular realRawDCTData realRawDCTLaws
    realPChiTableData realPChiTableLaws realRawTableTrivialization

/-- The completed computable table trivialization certificate. -/
def realNuBetaTableCertificate :
    NuBeta realRawDCT realPChiTableCertificate :=
  nuBetaOfRegular realRawDCT realPChiTableCertificate
    realRawTableTrivialization

/-! ## Exposed executable formulas -/

/-- The table binary regrading is literally the saved parity-shift table. -/
theorem realNuBetaTable_nu_eq_realLeanNuTable :
    realNuBetaTableCertificate.data.nu = realLeanNuTable :=
  rfl

/-- The table connector rescaling is the saved dyadic table under the
computable real-unit realization. -/
theorem realNuBetaTable_beta_eq_realLeanBetaTable
    (a b c : RawDCTGroup) :
    realNuBetaTableCertificate.data.beta a b c =
      dyadicRealHom (realLeanBetaTable a b c) :=
  rfl

/-! ## Closed nontrivial evaluations -/

/-- The table parity shift is genuinely nonzero. -/
example :
    realNuBetaTableCertificate.data.nu
      (Multiplicative.ofAdd 1) (Multiplicative.ofAdd 1) = 1 :=
  rfl

/-- The table package exposes its exact saved scalar at `(4,4,4)`. -/
example :
    realNuBetaTableCertificate.data.beta
      (Multiplicative.ofAdd 4) (Multiplicative.ofAdd 4)
      (Multiplicative.ofAdd 4) =
        dyadicRealHom
          (realLeanBetaTable
            (Multiplicative.ofAdd 4) (Multiplicative.ofAdd 4)
            (Multiplicative.ofAdd 4)) :=
  rfl

end Superfusion.RMod.RawDCT
