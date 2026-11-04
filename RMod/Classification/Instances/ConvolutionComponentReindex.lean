import RMod.Classification.Instances.ConvolutionComponentComparison

/-! # Naming the right input degree in the component comparison -/

set_option autoImplicit false

namespace RMod.Classification

noncomputable def convolutionComponentReindexData
    (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
    (X Y : PullbackObj C t) (k g h : t.group) (e : g⁻¹ * k = h) :
    IsoData C.toWeaklyPointedSuperfusionData (convolutionObj C hC t X Y k).val
      (C.tensorObj (X g).val (Y h).val) :=
  (convolutionComponentComparisonData C hC t X Y k g).trans C.toWeaklyPointedSuperfusionData
    (IsoData.ofEq C.toWeaklyPointedSuperfusionData
      (congrArg (fun l => C.tensorObj (X g).val (Y l).val) e))

end RMod.Classification
