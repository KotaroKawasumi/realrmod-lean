import RMod.BrundanEllis.StackingExternalBinaryBlock
import RMod.Classification.Instances.ConvolutionExpansion

/-! Assemble the actual binary component comparisons over all support
labels. The comparison uses the chosen convolution sums via their even
biproduct isomorphisms; both directions are specified. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace RMod.BrundanEllis.Stacking
open RMod.Classification CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

/-- Distribute both original convolution sums, retaining the external support order. -/
def exteriorConvolutionExpand (s t : Twist) (X X' : pullback s) (Y Y' : pullback t)
    (g : s.group) (h : t.group) :
    referenceEvenObj reference.data referenceProperty
      (reference.data.tensorObj
        (convolutionObj reference.data referenceProperty (oldTwist t).data Y Y' h).val
        (convolutionObj reference.data referenceProperty (oldTwist s).data X X' g).val) ≅
    ⨁ (fun gh : s.group × t.group =>
      convolutionEvenFamily reference.data referenceProperty (oldTwist t).data Y Y' h gh.2 ⊗
        convolutionEvenFamily reference.data referenceProperty (oldTwist s).data X X' g gh.1) :=
  tensorIso (convolutionEvenIso reference.data referenceProperty (oldTwist t).data Y Y' h)
      (convolutionEvenIso reference.data referenceProperty (oldTwist s).data X X' g) ≪≫
    leftDistributor _ (convolutionEvenFamily reference.data referenceProperty (oldTwist s).data X X' g) ≪≫
    biproduct.mapIso (fun a => rightDistributor
      (convolutionEvenFamily reference.data referenceProperty (oldTwist t).data Y Y' h)
      (convolutionEvenFamily reference.data referenceProperty (oldTwist s).data X X' g a)) ≪≫
    biproductBiproductIso (fun _ : s.group => t.group) (fun a b =>
      convolutionEvenFamily reference.data referenceProperty (oldTwist t).data Y Y' h b ⊗
        convolutionEvenFamily reference.data referenceProperty (oldTwist s).data X X' g a) ≪≫
    biproduct.whiskerEquiv
      (f := fun gh : (_ : s.group) × t.group =>
        convolutionEvenFamily reference.data referenceProperty (oldTwist t).data Y Y' h gh.2 ⊗
          convolutionEvenFamily reference.data referenceProperty (oldTwist s).data X X' g gh.1)
      (g := fun gh : s.group × t.group =>
        convolutionEvenFamily reference.data referenceProperty (oldTwist t).data Y Y' h gh.2 ⊗
          convolutionEvenFamily reference.data referenceProperty (oldTwist s).data X X' g gh.1)
      (Equiv.sigmaEquivProd s.group t.group) (fun _ => Iso.refl _)

/-- The single-summand comparison as an even-category isomorphism. -/
def exteriorConvolutionBlockIso (s t : Twist) (X X' : pullback s) (Y Y' : pullback t)
    (g : s.group) (h : t.group) (gh : s.group × t.group) :
    convolutionEvenFamily reference.data referenceProperty (oldTwist (exteriorTwist s t).val).data
      ((reversedExteriorPairing s t).obj (X, Y)) ((reversedExteriorPairing s t).obj (X', Y')) (g, h) gh ≅
    convolutionEvenFamily reference.data referenceProperty (oldTwist t).data Y Y' h gh.2 ⊗
      convolutionEvenFamily reference.data referenceProperty (oldTwist s).data X X' g gh.1 :=
  (exteriorBinaryBlockData s t X X' Y Y' gh.1 (gh.1⁻¹ * g) gh.2 (gh.2⁻¹ * h)).toEvenIso
    ⟨reference.data.toWeaklyPointedSuperfusionData, referenceProperty.toWeaklyPointedSuperfusionLaws⟩
    (exteriorBinaryBlockLaws s t X X' Y Y' gh.1 (gh.1⁻¹ * g) gh.2 (gh.2⁻¹ * h))

/-- The tensor comparison before checking unit and associator coherence. -/
def exteriorTensoratorEvenIso (s t : Twist) (X X' : pullback s) (Y Y' : pullback t)
    (g : s.group) (h : t.group) :
    referenceEvenObj reference.data referenceProperty
      (convolutionObj reference.data referenceProperty (oldTwist (exteriorTwist s t).val).data
        ((reversedExteriorPairing s t).obj (X, Y)) ((reversedExteriorPairing s t).obj (X', Y')) (g, h)).val ≅
    referenceEvenObj reference.data referenceProperty
      (reference.data.tensorObj
        (convolutionObj reference.data referenceProperty (oldTwist t).data Y Y' h).val
        (convolutionObj reference.data referenceProperty (oldTwist s).data X X' g).val) :=
  convolutionEvenIso reference.data referenceProperty (oldTwist (exteriorTwist s t).val).data _ _ (g, h) ≪≫
    biproduct.mapIso (exteriorConvolutionBlockIso s t X X' Y Y' g h) ≪≫
    (exteriorConvolutionExpand s t X X' Y Y' g h).symm

/-- Both raw comparison maps are extracted from the explicitly assembled even iso. -/
def exteriorTensoratorData (s t : Twist) (X X' : pullback s) (Y Y' : pullback t)
    (g : s.group) (h : t.group) :=
  IsoData.ofEvenIso
    ⟨reference.data.toWeaklyPointedSuperfusionData, referenceProperty.toWeaklyPointedSuperfusionLaws⟩
    (exteriorTensoratorEvenIso s t X X' Y Y' g h)

theorem exteriorTensoratorLaws (s t : Twist) (X X' : pullback s) (Y Y' : pullback t)
    (g : s.group) (h : t.group) :
    EvenIsoLaws reference.data.toWeaklyPointedSuperfusionData (exteriorTensoratorData s t X X' Y Y' g h) :=
  evenIsoLaws_ofEvenIso
    ⟨reference.data.toWeaklyPointedSuperfusionData, referenceProperty.toWeaklyPointedSuperfusionLaws⟩
    (exteriorTensoratorEvenIso s t X X' Y Y' g h)

end RMod.BrundanEllis.Stacking
