import RMod.Classification.Instances.EquivalenceTensorComparisonData
import RMod.Classification.Instances.ConvolutionIndexedTripleComparisons

/-!
# Evaluation comparisons for an equivalence at fixed target degrees

Use the given inverse tensorator followed by the actual target convolution
comparison. Nested composites retain these maps on both parenthesizations.
All support and coherence conditions belong to the separate proofs.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (twistedPullback C hC t).toWeaklyPointedSuperfusion)

noncomputable def equivalenceIndexedComparisonData (X Y : PullbackObj C s.data)
    (g h u : t.data.group) (e : g * h = u) :=
  (equivalenceTensoratorComponentData C hC s t E X Y u).trans C.toWeaklyPointedSuperfusionData
    (convolutionIndexedComparisonData C hC t.data (E.data.forward.obj X) (E.data.forward.obj Y) g h u e)

noncomputable def equivalenceIndexedLeftComparisonData (X Y Z : PullbackObj C s.data)
    (g h k u w : t.data.group) (eu : g * h = u) (ew : u * k = w) :=
  (equivalenceIndexedComparisonData C hC s t E ((twistedPullback C hC s).data.tensorObj X Y) Z u k w ew).trans
    C.toWeaklyPointedSuperfusionData
      ((equivalenceIndexedComparisonData C hC s t E X Y g h u eu).tensor C.toWeaklyPointedSuperfusionData
        (IsoData.refl C.toWeaklyPointedSuperfusionData (E.data.forward.obj Z k).val))

noncomputable def equivalenceIndexedRightComparisonData (X Y Z : PullbackObj C s.data)
    (g h k v w : t.data.group) (ev : h * k = v) (ew : g * v = w) :=
  ((equivalenceIndexedComparisonData C hC s t E X ((twistedPullback C hC s).data.tensorObj Y Z) g v w ew).trans
    C.toWeaklyPointedSuperfusionData
      ((IsoData.refl C.toWeaklyPointedSuperfusionData (E.data.forward.obj X g).val).tensor
        C.toWeaklyPointedSuperfusionData (equivalenceIndexedComparisonData C hC s t E Y Z h k v ev))).trans
    C.toWeaklyPointedSuperfusionData ((IsoData.assoc C.toWeaklyPointedSuperfusionData
      (E.data.forward.obj X g).val (E.data.forward.obj Y h).val (E.data.forward.obj Z k).val).symm
        C.toWeaklyPointedSuperfusionData)

end RMod.Classification
