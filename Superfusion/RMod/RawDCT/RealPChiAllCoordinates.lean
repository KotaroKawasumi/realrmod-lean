import Superfusion.RMod.RawDCT.RealPChiTableActual

/-!
# Actual pentagon equality at every real kernel coordinate

The soundness theorem for the computable real table is an equality of the
actual semantic top and bottom routes.  Evaluating that equality first on an
arbitrary kernel source generator and then at an arbitrary kernel target
coordinate proves the corresponding equality of executable coefficients.

No finite fourfold route is recomputed here.  The two semantic coordinate
bridges turn the already-proved route equality into exact real, rational,
and denominator-cleared integer identities.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiAllCoordinates

open GaugeChi
open RealPChiKernel

/-! ## Every coordinate of the actual route equality -/

/-- At every source/target coordinate, the actual top kernel coefficient is
the frozen computable table value times the actual bottom coefficient.

This is obtained from the full semantic route equality
`realPChiTable_isSound`; the proof performs no pointwise coefficient
search and no finite `decide` computation. -/
theorem cast_topCoeff_eq_tableValue_mul_cast_botCoeff
    (a b c d : ZMod 8)
    (source : QuadSource a b c d)
    (target : QuadTarget a b c d) :
    ((topCoeff a b c d source target : ℤ) : ℝ) =
      ((RealPChiCertificate.tableValue a b c d : ℚ) : ℝ) *
        ((botCoeff a b c d source target : ℤ) : ℝ) := by
  have hroute := realPChiTable_isSound a b c d
  have hcoord := congrArg
    (fun f =>
      RealPChiRouteBridge.semanticObserve a b c d target
        (f (RealPChiRouteBridge.semanticSource a b c d source)))
    hroute
  rw [show
    RealPChiRouteBridge.semanticObserve a b c d target
        (famTop ℝ realGauge
          realConnectorRealization.toConnectorFamily a b c d
          (RealPChiRouteBridge.semanticSource a b c d source)) =
      ((topCoeff a b c d source target : ℤ) : ℝ) by
        simpa [ConnectorRealization.toConnectorFamily,
          ConnectorRealization.toConnectorFamilyOfData,
          realConnectorRealization, realConnectorRealizationData] using
          RealPChiRouteTop.semanticObserve_famTop
            a b c d source target] at hcoord
  simp only [LinearMap.smul_apply, map_smul, smul_eq_mul] at hcoord
  rw [RealPChiRouteBottom.semanticObserve_famBot] at hcoord
  rw [show
    ((realPChiTableData.chi
        (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
        (Multiplicative.ofAdd c) (Multiplicative.ofAdd d) : ℝˣ) : ℝ) =
      ((RealPChiCertificate.tableValue a b c d : ℚ) : ℝ) by rfl] at hcoord
  exact hcoord

/-! ## Exact arithmetic consequences -/

/-- Injectivity of the rational embedding into the reals gives the exact
rational identity at every coordinate. -/
theorem cast_topCoeff_eq_tableValue_mul_cast_botCoeff_rat
    (a b c d : ZMod 8)
    (source : QuadSource a b c d)
    (target : QuadTarget a b c d) :
    ((topCoeff a b c d source target : ℤ) : ℚ) =
      RealPChiCertificate.tableValue a b c d *
        ((botCoeff a b c d source target : ℤ) : ℚ) := by
  exact_mod_cast
    cast_topCoeff_eq_tableValue_mul_cast_botCoeff
      a b c d source target

/-- Clearing the reduced positive denominator of the table value yields an
identity entirely in the integer coefficient kernel. -/
theorem tableValue_den_mul_topCoeff_eq_num_mul_botCoeff
    (a b c d : ZMod 8)
    (source : QuadSource a b c d)
    (target : QuadTarget a b c d) :
    ((RealPChiCertificate.tableValue a b c d).den : ℤ) *
        topCoeff a b c d source target =
      (RealPChiCertificate.tableValue a b c d).num *
        botCoeff a b c d source target := by
  let q := RealPChiCertificate.tableValue a b c d
  have hq :
      ((topCoeff a b c d source target : ℤ) : ℚ) =
        q * ((botCoeff a b c d source target : ℤ) : ℚ) :=
    cast_topCoeff_eq_tableValue_mul_cast_botCoeff_rat
      a b c d source target
  have hclear :
      (q.den : ℚ) * ((topCoeff a b c d source target : ℤ) : ℚ) =
        (q.num : ℚ) * ((botCoeff a b c d source target : ℤ) : ℚ) := by
    calc
      (q.den : ℚ) * ((topCoeff a b c d source target : ℤ) : ℚ) =
          ((topCoeff a b c d source target : ℤ) : ℚ) *
            (q.den : ℚ) := by ring
      _ = (q * ((botCoeff a b c d source target : ℤ) : ℚ)) *
          (q.den : ℚ) := by rw [hq]
      _ = (q * (q.den : ℚ)) *
          ((botCoeff a b c d source target : ℤ) : ℚ) := by ring
      _ = (q.num : ℚ) *
          ((botCoeff a b c d source target : ℤ) : ℚ) := by
            rw [Rat.mul_den_eq_num]
  exact_mod_cast hclear

/-! ## Nontrivial closed table sectors -/

/-- Every coordinate in the all-four sector has top coefficient four times
its bottom coefficient. -/
example (source : QuadSource 4 4 4 4) (target : QuadTarget 4 4 4 4) :
    ((topCoeff 4 4 4 4 source target : ℤ) : ℚ) =
      4 * ((botCoeff 4 4 4 4 source target : ℤ) : ℚ) := by
  have htable : RealPChiCertificate.tableValue 4 4 4 4 = 4 := by
    decide +kernel
  simpa [htable] using
    cast_topCoeff_eq_tableValue_mul_cast_botCoeff_rat
      4 4 4 4 source target

/-- Every coordinate in the all-five sector has top coefficient eight times
its bottom coefficient. -/
example (source : QuadSource 5 5 5 5) (target : QuadTarget 5 5 5 5) :
    ((topCoeff 5 5 5 5 source target : ℤ) : ℚ) =
      8 * ((botCoeff 5 5 5 5 source target : ℤ) : ℚ) := by
  have htable : RealPChiCertificate.tableValue 5 5 5 5 = 8 := by
    decide +kernel
  simpa [htable] using
    cast_topCoeff_eq_tableValue_mul_cast_botCoeff_rat
      5 5 5 5 source target

end RealPChiAllCoordinates
end Superfusion.RMod.RawDCT
