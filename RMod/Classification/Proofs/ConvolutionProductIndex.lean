import RMod.Classification.Proofs.ConvolutionProductInsertions

/-!
# Moving a product-indexed inclusion to a specified output degree

Any proof `g*h=k` identifies the output convolution objects. Moving
that equality comparison to the source of the inclusion gives exactly
the complementary-degree comparison used by the fixed-output inclusion.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

theorem convolutionProductInclusion_index (X Y : PullbackObj C t)
    (g h k : t.group) (e : g * h = k) (eh : h = g⁻¹ * k) :
    C.comp (convolutionProductInclusion C hC t X Y g h)
      (IsoData.ofEq C.toWeaklyPointedSuperfusionData
        (congrArg (fun q => (convolutionObj C hC t X Y q).val) e)).hom =
    C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData
      (congrArg (twistSummand C t X Y g) eh)).hom
      (convolutionInclusion C hC t X Y k g) := by
  subst k
  exact hC.comp_id _

end RMod.Classification
