import Superfusion.RMod.RawDCT.PChiOfConnector

/-!
# Soundness certificates for raw obstruction tables

This file contains the abstract bridge from a proposed unit-valued
four-cochain to the actual fourfold defect of a realized raw connector.
For each quadruple, a certificate selects one source vector and one scalar
observation on the target.  Its laws say that the observed bottom route is
nonzero and that the proposed table entry is the observed top-to-bottom
ratio.

The bridge itself performs no finite route calculation.  It consumes those
two laws with the existing one-dimensional route theorem
`chiOfFamily_eq_of_separating` and thereby identifies the proposed value
with `chiOfFamily`.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT

open GaugeChi

/-! ## Pointwise observation data -/

/-- Computational witnesses used to observe one nonzero coordinate of each
fourfold route comparison.

The selected source vectors and target functionals are data because a
finite certificate evaluator must be able to apply them.  No equality or
nonvanishing assertion is stored at this layer. -/
structure PChiSoundnessData
    (Gamma : DivisionFusionGauge ℝ (ZMod 8)) where
  source : ∀ a b c d : ZMod 8, GQ1 ℝ Gamma a b c d
  observe : ∀ a b c d : ZMod 8, GQ4 ℝ Gamma a b c d →ₗ[ℝ] ℝ

/-! ## Laws of an observation certificate -/

/-- The laws certifying that the exact table `pchi` is the fourfold defect
of the connector in `R`.

The first law makes the selected observation separating.  The second law
is the sole numerical certificate obligation: at that observation, the top
route is the proposed table scalar times the bottom route. -/
structure PChiSoundnessLaws {X : RawDCT}
    (Gamma : DivisionFusionGauge ℝ (ZMod 8))
    (R : ConnectorRealization X Gamma) (pchi : PChiData)
    (d : PChiSoundnessData Gamma) : Prop where
  bottom_ne_zero : ∀ a b c e,
    d.observe a b c e
        (famBot ℝ Gamma R.toConnectorFamily a b c e
          (d.source a b c e)) ≠ 0
  top_eq : ∀ a b c e,
    d.observe a b c e
        (famTop ℝ Gamma R.toConnectorFamily a b c e
          (d.source a b c e)) =
      ((pchi.chi
          (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
          (Multiplicative.ofAdd c) (Multiplicative.ofAdd e) : ℝˣ) : ℝ) *
        d.observe a b c e
          (famBot ℝ Gamma R.toConnectorFamily a b c e
            (d.source a b c e))

/-! ## Completed soundness certificate -/

/-- Observation data bundled with laws about that exact data and the exact
proposed obstruction table. -/
structure PChiSoundness {X : RawDCT}
    (Gamma : DivisionFusionGauge ℝ (ZMod 8))
    (R : ConnectorRealization X Gamma) (pchi : PChiData) where
  data : PChiSoundnessData Gamma
  laws : PChiSoundnessLaws Gamma R pchi data

/-! ## Route-level soundness -/

/-- Pure route-level actuality of a proposed obstruction table.  This is a
property rather than a data-bearing mathematical structure, so it does not
need a separate Data--Laws bundle. -/
def IsPChiSound {X : RawDCT}
    {Gamma : DivisionFusionGauge ℝ (ZMod 8)}
    (R : ConnectorRealization X Gamma) (pchi : PChiData) : Prop :=
  ∀ a b c e,
    famTop ℝ Gamma R.toConnectorFamily a b c e =
      ((pchi.chi
          (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
          (Multiplicative.ofAdd c) (Multiplicative.ofAdd e) : ℝˣ) : ℝ) •
        famBot ℝ Gamma R.toConnectorFamily a b c e

namespace PChiSoundness

variable {X : RawDCT} {Gamma : DivisionFusionGauge ℝ (ZMod 8)}
variable {R : ConnectorRealization X Gamma} {pchi : PChiData}

/-! ## The abstract soundness bridge -/

/-- One separating observation identifies a proposed table entry with the
semantic scalar selected by the existing fourfold route theorem. -/
theorem chi_val (s : PChiSoundness Gamma R pchi) (a b c e : ZMod 8) :
    ((pchi.chi
        (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
        (Multiplicative.ofAdd c) (Multiplicative.ofAdd e) : ℝˣ) : ℝ) =
      chiOfFamily ℝ Gamma R.toConnectorFamily a b c e := by
  symm
  exact chiOfFamily_eq_of_separating ℝ Gamma R.toConnectorFamily _
    (s.data.source a b c e) (s.data.observe a b c e)
    (s.laws.bottom_ne_zero a b c e) (s.laws.top_eq a b c e)

/-- A completed observation certificate implies the full route identity;
the full identity is obtained from the already-proved defining equation of
`chiOfFamily`, not by comparing route matrices again. -/
theorem isSound (s : PChiSoundness Gamma R pchi) : IsPChiSound R pchi := by
  intro a b c e
  rw [s.chi_val a b c e]
  exact famTop_eq_smul_famBot ℝ Gamma R.toConnectorFamily a b c e

end PChiSoundness

/-! ## Consumers of route-level soundness -/

/-- Route-level soundness is equivalent to pointwise equality with the
unique semantic pentagon scalar. -/
theorem isPChiSound_iff_chi_val {X : RawDCT}
    {Gamma : DivisionFusionGauge ℝ (ZMod 8)}
    (R : ConnectorRealization X Gamma) (pchi : PChiData) :
    IsPChiSound R pchi ↔
      ∀ a b c e,
        ((pchi.chi
            (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
            (Multiplicative.ofAdd c) (Multiplicative.ofAdd e) : ℝˣ) : ℝ) =
          chiOfFamily ℝ Gamma R.toConnectorFamily a b c e := by
  constructor
  · intro h a b c e
    symm
    exact chiOfFamily_eq_of_routes ℝ Gamma R.toConnectorFamily _
      (h a b c e)
  · intro h a b c e
    rw [h a b c e]
    exact famTop_eq_smul_famBot ℝ Gamma R.toConnectorFamily a b c e

/-- The obstruction constructed from a connector realization is sound by
the existing semantic fourfold theorem. -/
theorem pChiDataOfConnectorRealization_isSound {X : RawDCT}
    {Gamma : DivisionFusionGauge ℝ (ZMod 8)}
    (R : ConnectorRealization X Gamma) :
    IsPChiSound R (pChiDataOfConnectorRealization R) :=
  pChiDataOfConnectorRealization_actual R

/-- Two proposed obstruction tables sound for the same realized connector
have identical scalar cochains. -/
theorem chi_eq_of_isPChiSound {X : RawDCT}
    {Gamma : DivisionFusionGauge ℝ (ZMod 8)}
    {R : ConnectorRealization X Gamma} {pchi qchi : PChiData}
    (hp : IsPChiSound R pchi) (hq : IsPChiSound R qchi) :
    pchi.chi = qchi.chi := by
  funext a b c e
  apply Units.ext
  exact ((isPChiSound_iff_chi_val R pchi).mp hp
    a.toAdd b.toAdd c.toAdd e.toAdd).trans
      ((isPChiSound_iff_chi_val R qchi).mp hq
        a.toAdd b.toAdd c.toAdd e.toAdd).symm

/-- Soundness determines the whole `PChiData`, since its only field is the
unit-valued scalar cochain. -/
theorem eq_of_isPChiSound {X : RawDCT}
    {Gamma : DivisionFusionGauge ℝ (ZMod 8)}
    {R : ConnectorRealization X Gamma} {pchi qchi : PChiData}
    (hp : IsPChiSound R pchi) (hq : IsPChiSound R qchi) :
    pchi = qchi := by
  cases pchi
  cases qchi
  congr
  exact chi_eq_of_isPChiSound hp hq

end Superfusion.RMod.RawDCT
