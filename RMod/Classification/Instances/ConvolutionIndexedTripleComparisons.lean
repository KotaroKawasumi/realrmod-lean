import RMod.Classification.Instances.ConvolutionIndexedComparisons

/-!
# The two raw triple evaluation comparisons

Apply the outer binary evaluation before the inner evaluation. Both
routes end at the left-bracketed ordinary tensor product. The right
route therefore retains the inverse ordinary associator explicitly.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

noncomputable def convolutionIndexedLeftComparisonData (X Y Z : PullbackObj C t)
    (g h k u w : t.group) (eu : g * h = u) (ew : u * k = w) :
    IsoData C.toWeaklyPointedSuperfusionData
      (convolutionObj C hC t (convolutionObj C hC t X Y) Z w).val
      (C.tensorObj (C.tensorObj (X g).val (Y h).val) (Z k).val) :=
  (convolutionIndexedComparisonData C hC t (convolutionObj C hC t X Y) Z u k w ew).trans
    C.toWeaklyPointedSuperfusionData
    ((convolutionIndexedComparisonData C hC t X Y g h u eu).tensor
      C.toWeaklyPointedSuperfusionData (IsoData.refl C.toWeaklyPointedSuperfusionData (Z k).val))

noncomputable def convolutionIndexedRightComparisonData (X Y Z : PullbackObj C t)
    (g h k v w : t.group) (ev : h * k = v) (ew : g * v = w) :
    IsoData C.toWeaklyPointedSuperfusionData
      (convolutionObj C hC t X (convolutionObj C hC t Y Z) w).val
      (C.tensorObj (C.tensorObj (X g).val (Y h).val) (Z k).val) :=
  ((convolutionIndexedComparisonData C hC t X (convolutionObj C hC t Y Z) g v w ew).trans
    C.toWeaklyPointedSuperfusionData
    ((IsoData.refl C.toWeaklyPointedSuperfusionData (X g).val).tensor
      C.toWeaklyPointedSuperfusionData (convolutionIndexedComparisonData C hC t Y Z h k v ev))).trans
    C.toWeaklyPointedSuperfusionData
      ((IsoData.assoc C.toWeaklyPointedSuperfusionData (X g).val (Y h).val (Z k).val).symm
        C.toWeaklyPointedSuperfusionData)

end RMod.Classification
