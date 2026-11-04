import RMod.Classification.Instances.ConvolutionInsertions
import RMod.Classification.Instances.RightFactorDeletion

/-!
# The homogeneous binary comparison obtained by projection and deletion

At fixed left and output degrees, project onto the actual convolution
summand and delete its right parity factor. Its specified inverse inserts
the factor and then includes the summand. These maps will be invertible
when the left input has the selected support.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

noncomputable def convolutionComponentComparisonData (X Y : PullbackObj C t) (k g : t.group) :
    IsoData C.toWeaklyPointedSuperfusionData (convolutionObj C hC t X Y k).val
      (C.tensorObj (X g).val (Y (g⁻¹ * k)).val) :=
  (⟨convolutionProjection C hC t X Y k g, convolutionInclusion C hC t X Y k g⟩ :
    IsoData C.toWeaklyPointedSuperfusionData _ _).trans C.toWeaklyPointedSuperfusionData
      (C.pi.rightFactorDeletion (C.tensorObj (X g).val (Y (g⁻¹ * k)).val) (t.nu g (g⁻¹ * k)))

end RMod.Classification
