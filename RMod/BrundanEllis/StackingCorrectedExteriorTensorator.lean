import RMod.BrundanEllis.StackingExternalTensorator
import RMod.BrundanEllis.StackingExternalEvenComparison
import RMod.BrundanEllis.StackingDeletionCorrection

/-! The explicitly gauge-corrected exterior tensorator. Both the reference comparisons and the actual finite-sum assembly retain specified even inverse maps. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace RMod.BrundanEllis.Stacking

/-- The normalized binary scalar gauge in separate external labels. It
is the comparison gauge on the product group, written without reindexing. -/
def exteriorComparisonExponent (s t : Twist) (g g' : s.group) (h h' : t.group) : ZMod 2 :=
  bwPrimitive (s.rho g) * bwPrimitive (t.rho h') +
    (bwBit (s.rho g) * bwBit (t.rho h') * (s.nu g g' + t.nu h h') +
      (bwPrimitive (s.rho g) * bwBit (t.rho h') + bwBit (s.rho g) * bwPrimitive (t.rho h')))

/-- This displayed formula is the existing comparison gauge on the external group. -/
theorem exteriorComparisonExponent_data (s t : Twist)
    (g g' : s.group) (h h' : t.group) :
    let s' : TwistOn (FiniteGrp.of (s.group × t.group)) :=
      baseChange (MonoidHom.fst s.group t.group) ⟨s, rfl⟩
    let t' : TwistOn (FiniteGrp.of (s.group × t.group)) :=
      baseChange (MonoidHom.snd s.group t.group) ⟨t, rfl⟩
    exteriorComparisonExponent s t g g' h h' =
      comparisonGaugeExponent (fixedRho s') (fixedRho t') (fixedNu s') (fixedNu t') (g, h) (g', h') := rfl

/-- The correction is zero at either unit of the external group. -/
theorem exteriorComparisonExponent_normalized (s t : Twist) (g : s.group) (h : t.group) :
    exteriorComparisonExponent s t 1 g 1 h = 0 ∧
      exteriorComparisonExponent s t g 1 h 1 = 0 := by
  constructor <;> simp [exteriorComparisonExponent]

end RMod.BrundanEllis.Stacking

namespace RMod.BrundanEllis.Stacking
open RMod.Classification

/-- Scale the actual external binary comparison by the explicit normalized
gauge. Both directions are retained, using inverse real units. -/
def correctedExteriorBinaryData (s t : Twist) (X X' : pullback s) (Y Y' : pullback t)
    (g g' : s.group) (h h' : t.group) :=
  (exteriorBinaryBlockData s t X X' Y Y' g g' h h').scale
    reference.data.toWeaklyPointedSuperfusionData (realSign (exteriorComparisonExponent s t g g' h h'))

/-- Scalar gauge correction preserves the actual even isomorphism laws. -/
theorem correctedExteriorBinaryLaws (s t : Twist) (X X' : pullback s) (Y Y' : pullback t)
    (g g' : s.group) (h h' : t.group) :
    EvenIsoLaws reference.data.toWeaklyPointedSuperfusionData
      (correctedExteriorBinaryData s t X X' Y Y' g g' h h') :=
  EvenIsoLaws.scale referenceProperty.toWeaklyPointedSuperfusionLaws _
    (exteriorBinaryBlockLaws s t X X' Y Y' g g' h h')

end RMod.BrundanEllis.Stacking

namespace RMod.BrundanEllis.Stacking
open RMod.Classification CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

/-- The single-summand comparison as an even-category isomorphism. -/
def correctedExteriorConvolutionBlockIso (s t : Twist) (X X' : pullback s) (Y Y' : pullback t)
    (g : s.group) (h : t.group) (gh : s.group × t.group) :
    convolutionEvenFamily reference.data referenceProperty (oldTwist (exteriorTwist s t).val).data
      ((reversedExteriorPairing s t).obj (X, Y)) ((reversedExteriorPairing s t).obj (X', Y')) (g, h) gh ≅
    convolutionEvenFamily reference.data referenceProperty (oldTwist t).data Y Y' h gh.2 ⊗
      convolutionEvenFamily reference.data referenceProperty (oldTwist s).data X X' g gh.1 :=
  (correctedExteriorBinaryData s t X X' Y Y' gh.1 (gh.1⁻¹ * g) gh.2 (gh.2⁻¹ * h)).toEvenIso
    ⟨reference.data.toWeaklyPointedSuperfusionData, referenceProperty.toWeaklyPointedSuperfusionLaws⟩
    (correctedExteriorBinaryLaws s t X X' Y Y' gh.1 (gh.1⁻¹ * g) gh.2 (gh.2⁻¹ * h))

/-- The tensor comparison before checking unit and associator coherence. -/
def correctedExteriorTensoratorEvenIso (s t : Twist) (X X' : pullback s) (Y Y' : pullback t)
    (g : s.group) (h : t.group) :
    referenceEvenObj reference.data referenceProperty
      (convolutionObj reference.data referenceProperty (oldTwist (exteriorTwist s t).val).data
        ((reversedExteriorPairing s t).obj (X, Y)) ((reversedExteriorPairing s t).obj (X', Y')) (g, h)).val ≅
    referenceEvenObj reference.data referenceProperty
      (reference.data.tensorObj
        (convolutionObj reference.data referenceProperty (oldTwist t).data Y Y' h).val
        (convolutionObj reference.data referenceProperty (oldTwist s).data X X' g).val) :=
  convolutionEvenIso reference.data referenceProperty (oldTwist (exteriorTwist s t).val).data _ _ (g, h) ≪≫
    biproduct.mapIso (correctedExteriorConvolutionBlockIso s t X X' Y Y' g h) ≪≫
    (exteriorConvolutionExpand s t X X' Y Y' g h).symm

/-- Both raw comparison maps are extracted from the explicitly assembled even iso. -/
def correctedExteriorTensoratorData (s t : Twist) (X X' : pullback s) (Y Y' : pullback t)
    (g : s.group) (h : t.group) :=
  IsoData.ofEvenIso
    ⟨reference.data.toWeaklyPointedSuperfusionData, referenceProperty.toWeaklyPointedSuperfusionLaws⟩
    (correctedExteriorTensoratorEvenIso s t X X' Y Y' g h)

theorem correctedExteriorTensoratorLaws (s t : Twist) (X X' : pullback s) (Y Y' : pullback t)
    (g : s.group) (h : t.group) :
    EvenIsoLaws reference.data.toWeaklyPointedSuperfusionData (correctedExteriorTensoratorData s t X X' Y Y' g h) :=
  evenIsoLaws_ofEvenIso
    ⟨reference.data.toWeaklyPointedSuperfusionData, referenceProperty.toWeaklyPointedSuperfusionLaws⟩
    (correctedExteriorTensoratorEvenIso s t X X' Y Y' g h)

end RMod.BrundanEllis.Stacking

open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking

/-- The exterior tensor comparison as an isomorphism of whole pullback objects. -/
def correctedReversedExteriorTensorIso (s t : Twist)
    (X Y : Even (SuperTensorProduct (pullback s) (pullback t))) :
    (reversedExteriorPairing s t).forget.obj X ⊗ (reversedExteriorPairing s t).forget.obj Y ≅
      (reversedExteriorPairing s t).forget.obj (X ⊗ Y) :=
  pullbackCoordinateIso (exteriorTwist s t).val _ _
    (fun gh => correctedExteriorTensoratorEvenIso s t X.1 Y.1 X.2 Y.2 gh.1 gh.2)

/-- The assembled comparison has exactly the previously specified coordinate map. -/
theorem correctedReversedExteriorTensorIso_hom (s t : Twist)
    (X Y : Even (SuperTensorProduct (pullback s) (pullback t)))
    (g : s.group) (h : t.group) :
    pullbackEvenValue (exteriorTwist s t).val (correctedReversedExteriorTensorIso s t X Y).hom (g, h) =
      (correctedExteriorTensoratorData s t X.1 Y.1 X.2 Y.2 g h).hom := by
  unfold pullbackEvenValue correctedReversedExteriorTensorIso
  rw [pullbackCoordinateIso_hom]
  rfl

end RMod.BrundanEllis.Stacking
