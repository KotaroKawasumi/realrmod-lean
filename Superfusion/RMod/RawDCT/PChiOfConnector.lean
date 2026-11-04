import Superfusion.Cochain.HchiCore
import Superfusion.GaugeChi.QuadChase
import Superfusion.GaugeChi.QuintChain
import Superfusion.RMod.RawDCT.ConnectorRealization
import Superfusion.RMod.RawDCT.PChi

/-!
# The obstruction of a realized raw connector

This file derives `(p, chi)` from a raw DCT whose stored connector has been
identified with an existing semantic connector family.  The parity is the
parity already stored in `TData`.  The scalar is the actual fourfold defect:
the canonical defect multiplied by the coboundary of the pointwise connector
ratio.  `chiOfFamily_rescale_dm₃` identifies this formula with the scalar in
the existing top-versus-bottom route theorem.

No fourfold route is evaluated here.  The construction reuses the general
fourfold calculation in `ConnectorRescale.lean`.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT

open GaugeChi

/-! ## The connector ratio and its derived obstruction -/

/-- The three-cochain comparing the canonical connector with the connector
which realizes the stored raw `T`. -/
noncomputable def connectorRatioCochain {X : RawDCT}
    {Gamma : DivisionFusionGauge ℝ (ZMod 8)}
    (R : ConnectorRealization X Gamma) :
    RawDCTGroup → RawDCTGroup → RawDCTGroup → ℝˣ :=
  fun a b c => ConnectorFamily.ratio
    (ConnectorFamily.canonical ℝ Gamma) R.toConnectorFamily
    a.toAdd b.toAdd c.toAdd

/-- The actual unit-valued fourfold defect of the connector realizing `X`.

The formula is computationally transparent about its mathematical source,
but is noncomputable because the existing semantic connector ratio is chosen
from a one-dimensional intertwiner line. -/
noncomputable def pChiDataOfConnectorRealization {X : RawDCT}
    {Gamma : DivisionFusionGauge ℝ (ZMod 8)}
    (R : ConnectorRealization X Gamma) : PChiData where
  chi := fun a b c d =>
    gChiCanonCochain ℝ Gamma a b c d *
      Superfusion.dm₃ (connectorRatioCochain R) a b c d

/-! ## Identification with the stored raw parity and actual fourfold route -/

/-- The parity stored in the raw `T` is the intrinsic parity of its realized
semantic connector. -/
theorem rawParity_eq_gParityCochain {X : RawDCT}
    {Gamma : DivisionFusionGauge ℝ (ZMod 8)}
    (R : ConnectorRealization X Gamma) :
    rawParity X.data = gParityCochain ℝ Gamma := by
  funext a b c
  exact (R.laws.parity a.toAdd b.toAdd c.toAdd).trans
    (R.toConnectorFamily.parity_eq a.toAdd b.toAdd c.toAdd)

/-- The scalar stored by the derived `PChiData` is exactly the scalar of the
existing semantic top-versus-bottom fourfold route theorem. -/
theorem pChiDataOfConnectorRealization_chi_val {X : RawDCT}
    {Gamma : DivisionFusionGauge ℝ (ZMod 8)}
    (R : ConnectorRealization X Gamma) (a b c d : RawDCTGroup) :
    (((pChiDataOfConnectorRealization R).chi a b c d : ℝˣ) : ℝ) =
      chiOfFamily ℝ Gamma R.toConnectorFamily
        a.toAdd b.toAdd c.toAdd d.toAdd := by
  rw [chiOfFamily_rescale_dm₃ ℝ Gamma
    (ConnectorFamily.canonical ℝ Gamma) R.toConnectorFamily]
  rfl

/-- Route-level actuality of the derived scalar.  This is the existing
fourfold calculation specialized to the connector which is proved to be the
stored raw `T`. -/
theorem pChiDataOfConnectorRealization_actual {X : RawDCT}
    {Gamma : DivisionFusionGauge ℝ (ZMod 8)}
    (R : ConnectorRealization X Gamma) (a b c d : ZMod 8) :
    famTop ℝ Gamma R.toConnectorFamily a b c d =
      ((((pChiDataOfConnectorRealization R).chi
        (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
        (Multiplicative.ofAdd c) (Multiplicative.ofAdd d) : ℝˣ) : ℝ) •
          famBot ℝ Gamma R.toConnectorFamily a b c d) := by
  rw [pChiDataOfConnectorRealization_chi_val]
  exact famTop_eq_smul_famBot ℝ Gamma R.toConnectorFamily a b c d

/-! ## Supercocycle laws and completed obstruction -/

/-- The actual connector obstruction satisfies the Gu--Wen equations.  The
canonical equation is already proved by the fivefold route chase, and the
connector change contributes only a coboundary. -/
theorem pChiLawsOfConnectorRealization {X : RawDCT}
    {Gamma : DivisionFusionGauge ℝ (ZMod 8)}
    (R : ConnectorRealization X Gamma) :
    PChiLaws X.data X.laws (pChiDataOfConnectorRealization R) := by
  have hp : rawParity X.data = gParityCochain ℝ Gamma :=
    rawParity_eq_gParityCochain R
  refine {
    p_cocycle := ?_
    chi_supercocycle := ?_ }
  · intro a b c d
    rw [hp]
    exact gParityCochain_cocycle ℝ Gamma a b c d
  · intro a b c d e
    change
      Superfusion.dm₄
          (fun x y z w =>
            gChiCanonCochain ℝ Gamma x y z w *
              Superfusion.dm₃ (connectorRatioCochain R) x y z w)
          a b c d e = _
    rw [Superfusion.dm₄_mul,
      gChiCanon_supercocycle ℝ Gamma,
      Superfusion.dm₄_dm₃, mul_one, hp]

/-- Bundle the actual obstruction of a realized raw DCT. -/
noncomputable def pChiOfConnectorRealization {X : RawDCT}
    {Gamma : DivisionFusionGauge ℝ (ZMod 8)}
    (R : ConnectorRealization X Gamma) : PChi X where
  data := pChiDataOfConnectorRealization R
  laws := pChiLawsOfConnectorRealization R

end Superfusion.RMod.RawDCT
