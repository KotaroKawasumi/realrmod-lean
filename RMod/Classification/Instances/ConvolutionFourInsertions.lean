import RMod.Classification.Instances.ConvolutionTripleInsertions

/-!
# The five parenthesizations of four convolution summands

Each family keeps its parity factors in the positions specified by the
binary tensor construction. The inclusions are built from the chosen
binary and threefold inclusions. The three free indices record the
successive binary splits in the corresponding parenthesization.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits MonoidalCategory

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

def convolutionFourLeftFamily (W X Y Z : PullbackObj C t) (k a b c : t.group) :
    ReferenceEvenCategory C hC :=
  referenceEvenObj C hC (C.tensorObj
    (C.tensorObj (convolutionLeftFamily C hC t W X Y a b c).obj (Z (a⁻¹ * k)).val)
    (C.pi.factor (t.nu a (a⁻¹ * k))))

def convolutionFourInnerFamily (W X Y Z : PullbackObj C t) (k a b c : t.group) :
    ReferenceEvenCategory C hC :=
  referenceEvenObj C hC (C.tensorObj
    (C.tensorObj (convolutionRightFamily C hC t W X Y a b c).obj (Z (a⁻¹ * k)).val)
    (C.pi.factor (t.nu a (a⁻¹ * k))))

def convolutionFourMiddleFamily (W X Y Z : PullbackObj C t) (k a b c : t.group) :
    ReferenceEvenCategory C hC :=
  referenceEvenObj C hC (C.tensorObj
    (C.tensorObj (twistSummand C t W X b (b⁻¹ * a)) (twistSummand C t Y Z c (c⁻¹ * (a⁻¹ * k))))
    (C.pi.factor (t.nu a (a⁻¹ * k))))

def convolutionFourOuterFamily (W X Y Z : PullbackObj C t) (k a b c : t.group) :
    ReferenceEvenCategory C hC :=
  referenceEvenObj C hC (C.tensorObj
    (C.tensorObj (W a).val (convolutionLeftFamily C hC t X Y Z (a⁻¹ * k) b c).obj)
    (C.pi.factor (t.nu a (a⁻¹ * k))))

def convolutionFourRightFamily (W X Y Z : PullbackObj C t) (k a b c : t.group) :
    ReferenceEvenCategory C hC :=
  referenceEvenObj C hC (C.tensorObj
    (C.tensorObj (W a).val (convolutionRightFamily C hC t X Y Z (a⁻¹ * k) b c).obj)
    (C.pi.factor (t.nu a (a⁻¹ * k))))

attribute [local implicit_reducible] convolutionFourLeftFamily convolutionFourInnerFamily
  convolutionFourMiddleFamily convolutionFourOuterFamily convolutionFourRightFamily
  convolutionLeftFamily convolutionRightFamily convolutionEvenFamily twistSummand

noncomputable def convolutionFourLeftInsertion (W X Y Z : PullbackObj C t) (k a b c : t.group) :
    convolutionFourLeftFamily C hC t W X Y Z k a b c ⟶
      referenceEvenObj C hC
        (convolutionObj C hC t (convolutionObj C hC t (convolutionObj C hC t W X) Y) Z k).val :=
  ((convolutionLeftInsertionEven C hC t W X Y a b c ▷ referenceEvenObj C hC (Z (a⁻¹ * k)).val) ▷
    referenceEvenObj C hC (C.pi.factor (t.nu a (a⁻¹ * k)))) ≫
      convolutionInclusionEven C hC t (convolutionObj C hC t (convolutionObj C hC t W X) Y) Z k a

noncomputable def convolutionFourInnerInsertion (W X Y Z : PullbackObj C t) (k a b c : t.group) :
    convolutionFourInnerFamily C hC t W X Y Z k a b c ⟶
      referenceEvenObj C hC
        (convolutionObj C hC t (convolutionObj C hC t W (convolutionObj C hC t X Y)) Z k).val :=
  ((convolutionRightInsertionEven C hC t W X Y a b c ▷ referenceEvenObj C hC (Z (a⁻¹ * k)).val) ▷
    referenceEvenObj C hC (C.pi.factor (t.nu a (a⁻¹ * k)))) ≫
      convolutionInclusionEven C hC t (convolutionObj C hC t W (convolutionObj C hC t X Y)) Z k a

noncomputable def convolutionFourMiddleInsertion (W X Y Z : PullbackObj C t) (k a b c : t.group) :
    convolutionFourMiddleFamily C hC t W X Y Z k a b c ⟶
      referenceEvenObj C hC
        (convolutionObj C hC t (convolutionObj C hC t W X) (convolutionObj C hC t Y Z) k).val :=
  ((convolutionInclusionEven C hC t W X a b ⊗ₘ
      convolutionInclusionEven C hC t Y Z (a⁻¹ * k) c) ▷
    referenceEvenObj C hC (C.pi.factor (t.nu a (a⁻¹ * k)))) ≫
      convolutionInclusionEven C hC t (convolutionObj C hC t W X) (convolutionObj C hC t Y Z) k a

noncomputable def convolutionFourOuterInsertion (W X Y Z : PullbackObj C t) (k a b c : t.group) :
    convolutionFourOuterFamily C hC t W X Y Z k a b c ⟶
      referenceEvenObj C hC
        (convolutionObj C hC t W (convolutionObj C hC t (convolutionObj C hC t X Y) Z) k).val :=
  ((referenceEvenObj C hC (W a).val ◁ convolutionLeftInsertionEven C hC t X Y Z (a⁻¹ * k) b c) ▷
    referenceEvenObj C hC (C.pi.factor (t.nu a (a⁻¹ * k)))) ≫
      convolutionInclusionEven C hC t W (convolutionObj C hC t (convolutionObj C hC t X Y) Z) k a

noncomputable def convolutionFourRightInsertion (W X Y Z : PullbackObj C t) (k a b c : t.group) :
    convolutionFourRightFamily C hC t W X Y Z k a b c ⟶
      referenceEvenObj C hC
        (convolutionObj C hC t W (convolutionObj C hC t X (convolutionObj C hC t Y Z)) k).val :=
  ((referenceEvenObj C hC (W a).val ◁ convolutionRightInsertionEven C hC t X Y Z (a⁻¹ * k) b c) ▷
    referenceEvenObj C hC (C.pi.factor (t.nu a (a⁻¹ * k)))) ≫
      convolutionInclusionEven C hC t W (convolutionObj C hC t X (convolutionObj C hC t Y Z)) k a

end RMod.Classification
