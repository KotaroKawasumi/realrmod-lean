import RMod.Classification.Instances.ConvolutionTripleInsertions

/-!
# Convolution inclusions indexed by their input degrees

The ordinary convolution inclusion uses a fixed output degree and the
complementary degree `g^-1*k`. Transport only its source to obtain the
inclusion of the actual `(g,h)` summand in degree `g*h`. Nested tensor
products of these specified maps retain the left and right triple
product degrees separately.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

noncomputable def convolutionProductInclusion (X Y : PullbackObj C t) (g h : t.group) :
    C.Hom (twistSummand C t X Y g h) (convolutionObj C hC t X Y (g * h)).val :=
  C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData
    (congrArg (twistSummand C t X Y g) (inv_mul_cancel_left g h).symm)).hom
    (convolutionInclusion C hC t X Y (g * h) g)

noncomputable def convolutionProductLeftInsertion (X Y Z : PullbackObj C t) (g h k : t.group) :
    C.Hom
      (C.tensorObj (C.tensorObj (twistSummand C t X Y g h) (Z k).val)
        (C.pi.factor (t.nu (g * h) k)))
      (convolutionObj C hC t (convolutionObj C hC t X Y) Z ((g * h) * k)).val :=
  C.comp (C.tensorHom (C.tensorHom (convolutionProductInclusion C hC t X Y g h)
      (C.id (Z k).val)) (C.id (C.pi.factor (t.nu (g * h) k))))
    (convolutionProductInclusion C hC t (convolutionObj C hC t X Y) Z (g * h) k)

noncomputable def convolutionProductRightInsertion (X Y Z : PullbackObj C t) (g h k : t.group) :
    C.Hom
      (C.tensorObj (C.tensorObj (X g).val (twistSummand C t Y Z h k))
        (C.pi.factor (t.nu g (h * k))))
      (convolutionObj C hC t X (convolutionObj C hC t Y Z) (g * (h * k))).val :=
  C.comp (C.tensorHom (C.tensorHom (C.id (X g).val)
      (convolutionProductInclusion C hC t Y Z h k)) (C.id (C.pi.factor (t.nu g (h * k)))))
    (convolutionProductInclusion C hC t X (convolutionObj C hC t Y Z) g (h * k))

end RMod.Classification
