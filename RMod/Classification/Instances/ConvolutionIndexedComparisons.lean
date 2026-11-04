import RMod.Classification.Instances.ConvolutionComponentReindex
import RMod.Classification.Instances.ConvolutionIndexedProducts

/-!
# Binary evaluation at an explicitly named product degree

Keep the original convolution projection, inclusion, and parity deletion.
The equality witness only identifies the complementary input index with
the prescribed right degree. The inclusion also retains an explicit
inverse for use on supported families; its laws are proved separately.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

noncomputable def convolutionIndexedComparisonData (X Y : PullbackObj C t)
    (g h u : t.group) (e : g * h = u) :
    IsoData C.toWeaklyPointedSuperfusionData (convolutionObj C hC t X Y u).val
      (C.tensorObj (X g).val (Y h).val) :=
  convolutionComponentReindexData C hC t X Y u g h (inv_mul_eq_iff_eq_mul.mpr e.symm)

noncomputable def convolutionIndexedInclusionData (X Y : PullbackObj C t)
    (g h u : t.group) (e : g * h = u) :
    IsoData C.toWeaklyPointedSuperfusionData (twistSummand C t X Y g h)
      (convolutionObj C hC t X Y u).val :=
  (IsoData.ofEq C.toWeaklyPointedSuperfusionData
    (congrArg (twistSummand C t X Y g) (inv_mul_eq_iff_eq_mul.mpr e.symm).symm)).trans
    C.toWeaklyPointedSuperfusionData
      ⟨convolutionInclusion C hC t X Y u g, convolutionProjection C hC t X Y u g⟩

end RMod.Classification
