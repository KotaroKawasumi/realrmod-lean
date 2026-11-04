import RMod.Classification.Instances.ConvolutionBiproduct
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Distributing the two iterated convolutions

Mathlib's even tensor distributors and iterated biproduct isomorphism
expand both parenthesizations into sums indexed by two group variables.
The original chosen convolution sums are connected by their explicit
even biproduct comparisons. No coherence law is assumed for convolution.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

def convolutionLeftFamily (X Y Z : PullbackObj C t) (k a g : t.group) :
    ReferenceEvenCategory C hC :=
  referenceEvenObj C hC (C.tensorObj
    (C.tensorObj (twistSummand C t X Y g (g⁻¹ * a)) (Z (a⁻¹ * k)).val)
    (C.pi.factor (t.nu a (a⁻¹ * k))))

def convolutionRightFamily (X Y Z : PullbackObj C t) (k g h : t.group) :
    ReferenceEvenCategory C hC :=
  referenceEvenObj C hC (C.tensorObj
    (C.tensorObj (X g).val (twistSummand C t Y Z h (h⁻¹ * (g⁻¹ * k))))
    (C.pi.factor (t.nu g (g⁻¹ * k))))

attribute [local implicit_reducible] convolutionEvenFamily convolutionLeftFamily
  convolutionRightFamily twistSummand

noncomputable def convolutionLeftExpand (X Y Z : PullbackObj C t) (k : t.group) :
    referenceEvenObj C hC (convolutionObj C hC t (convolutionObj C hC t X Y) Z k).val ≅
      ⨁ (fun i : (_ : t.group) × t.group => convolutionLeftFamily C hC t X Y Z k i.1 i.2) :=
  convolutionEvenIso C hC t (convolutionObj C hC t X Y) Z k ≪≫
    biproduct.mapIso (fun a =>
      let W := referenceEvenObj C hC (Z (a⁻¹ * k)).val
      let P := referenceEvenObj C hC (C.pi.factor (t.nu a (a⁻¹ * k)))
      tensorIso (tensorIso (convolutionEvenIso C hC t X Y a) (CategoryTheory.Iso.refl W))
          (CategoryTheory.Iso.refl P) ≪≫
        tensorIso (rightDistributor (convolutionEvenFamily C hC t X Y a) W)
          (CategoryTheory.Iso.refl P) ≪≫
        rightDistributor (fun g => convolutionEvenFamily C hC t X Y a g ⊗ W) P) ≪≫
    biproductBiproductIso (fun _ : t.group => t.group) (convolutionLeftFamily C hC t X Y Z k)

noncomputable def convolutionRightExpand (X Y Z : PullbackObj C t) (k : t.group) :
    referenceEvenObj C hC (convolutionObj C hC t X (convolutionObj C hC t Y Z) k).val ≅
      ⨁ (fun i : (_ : t.group) × t.group => convolutionRightFamily C hC t X Y Z k i.1 i.2) :=
  convolutionEvenIso C hC t X (convolutionObj C hC t Y Z) k ≪≫
    biproduct.mapIso (fun g =>
      let W := referenceEvenObj C hC (X g).val
      let P := referenceEvenObj C hC (C.pi.factor (t.nu g (g⁻¹ * k)))
      tensorIso (tensorIso (CategoryTheory.Iso.refl W) (convolutionEvenIso C hC t Y Z (g⁻¹ * k)))
          (CategoryTheory.Iso.refl P) ≪≫
        tensorIso (leftDistributor W (convolutionEvenFamily C hC t Y Z (g⁻¹ * k)))
          (CategoryTheory.Iso.refl P) ≪≫
        rightDistributor (fun h => W ⊗ convolutionEvenFamily C hC t Y Z (g⁻¹ * k) h) P) ≪≫
    biproductBiproductIso (fun _ : t.group => t.group) (convolutionRightFamily C hC t X Y Z k)

end RMod.Classification
