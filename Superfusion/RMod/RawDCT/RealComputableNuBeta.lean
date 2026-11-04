import Superfusion.RMod.RawDCT.RealPChiTableActual

/-!
# Computable real obstruction trivialization

The exact route certificate identifies the frozen `(p, chi)` table with the
actual obstruction of `realRawDCT`.  Consequently the already proved frozen
`(nu, beta)` laws may now be exposed as a computable trivialization of a
computable presentation of that actual obstruction.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT

open GaugeChi

/-! ## Concrete computable bundle -/

/-- The executable `(nu, beta)` table, now indexed by the computable
presentation of the actual `(p, chi)`. -/
def realComputableNuBeta : NuBeta realRawDCT realComputablePChi :=
  realNuBetaTableCertificate

/-- The same executable data satisfy the laws indexed by the original
semantic name `realPChi`.  Only the law proof is transported across the
actuality theorem; the `NuBetaData` fields are not transported. -/
theorem realComputableNuBetaActualLaws :
    NuBetaLaws realRawDCT.data realRawDCT.laws
      realPChi.data realPChi.laws realNuBetaTableData := by
  rw [← realPChiTableCertificate_eq_realPChi]
  exact realNuBetaTableLaws

/-- A completed `(nu, beta)` for `realPChi` whose computational fields are
still literally the finite tables. -/
def realComputableNuBetaActual : NuBeta realRawDCT realPChi where
  data := realNuBetaTableData
  laws := realComputableNuBetaActualLaws

/-! ## Exposed computational fields -/

/-- The binary regrading is literally the saved finite table. -/
theorem realComputableNuBeta_nu_eq_realLeanNuTable :
    realComputableNuBeta.data.nu = realLeanNuTable :=
  rfl

/-- The connector rescaling is literally the saved dyadic table under its
explicit real-unit realization. -/
theorem realComputableNuBeta_beta_eq_realLeanBetaTable
    (a b c : RawDCTGroup) :
    realComputableNuBeta.data.beta a b c =
      dyadicRealHom (realLeanBetaTable a b c) :=
  rfl

/-- Reindexing by the semantic name of the actual obstruction does not
change the executable fields. -/
theorem realComputableNuBetaActual_data_eq :
    realComputableNuBetaActual.data = realComputableNuBeta.data :=
  rfl

/-! ## Closed nontrivial evaluations -/

/-- The computable parity shift is nonzero at `(1,1)`. -/
example :
    realComputableNuBeta.data.nu
      (Multiplicative.ofAdd 1) (Multiplicative.ofAdd 1) = 1 :=
  rfl

/-- The computable rescaling retains the nontrivial saved entry at
`(4,4,4)`. -/
example :
    realComputableNuBeta.data.beta
      (Multiplicative.ofAdd 4) (Multiplicative.ofAdd 4)
      (Multiplicative.ofAdd 4) =
        dyadicRealHom
          (realLeanBetaTable
            (Multiplicative.ofAdd 4) (Multiplicative.ofAdd 4)
            (Multiplicative.ofAdd 4)) :=
  rfl

end Superfusion.RMod.RawDCT
