import RMod.Classification.Instances.GaugeIndexedBinaryComparison

/-!
# Triple evaluation transported by the selected component comparisons

Both routes start with the same inverse comparison on the left-associated
source product and end with the same tensor of the three input comparisons.
The right route retains the given functor image of the source associator.
Every inverse, including tensor crossing signs, is part of the data.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (twistedPullback C hC t).toWeaklyPointedSuperfusion)
  (g h k : s.data.group)
  (X : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (pullbackDegreeSimple C hC s g).data.object)
  (Y : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (pullbackDegreeSimple C hC s h).data.object)
  (Z : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (pullbackDegreeSimple C hC s k).data.object)

noncomputable def equivalenceNamedTripleInputComparisonData :=
  ((equivalenceNamedComparisonData C hC s t E g X).homogeneousTensor C.toWeaklyPointedSuperfusionData
    (equivalenceGaugeLambda C hC s t E g) (equivalenceGaugeLambda C hC s t E h)
    (equivalenceNamedComparisonData C hC s t E h Y)).homogeneousTensor C.toWeaklyPointedSuperfusionData
      (equivalenceGaugeLambda C hC s t E g + equivalenceGaugeLambda C hC s t E h)
      (equivalenceGaugeLambda C hC s t E k) (equivalenceNamedComparisonData C hC s t E k Z)

noncomputable def equivalenceIndexedLeftTransportData (u w : s.data.group)
    (eu : g * h = u) (ew : u * k = w) :
    IsoData C.toWeaklyPointedSuperfusionData
      (convolutionObj C hC s.data (convolutionObj C hC s.data X.obj Y.obj) Z.obj w).val
      (C.tensorObj (C.tensorObj (X.obj g).val (Y.obj h).val) (Z.obj k).val) :=
  (((equivalenceNamedComparisonData C hC s t E w
    (pullbackIndexedTensorSpanObj C hC s u k w ew
      (pullbackIndexedTensorSpanObj C hC s g h u eu X Y) Z)).symm C.toWeaklyPointedSuperfusionData).trans
    C.toWeaklyPointedSuperfusionData
    (equivalenceIndexedLeftComparisonData C hC s t E X.obj Y.obj Z.obj
      (equivalenceGaugePhi C hC s t E g) (equivalenceGaugePhi C hC s t E h)
      (equivalenceGaugePhi C hC s t E k) (equivalenceGaugePhi C hC s t E u)
      (equivalenceGaugePhi C hC s t E w)
      ((map_mul (equivalenceGaugePhi C hC s t E) g h).symm.trans
        (congrArg (equivalenceGaugePhi C hC s t E) eu))
      ((map_mul (equivalenceGaugePhi C hC s t E) u k).symm.trans
        (congrArg (equivalenceGaugePhi C hC s t E) ew)))).trans C.toWeaklyPointedSuperfusionData
      (equivalenceNamedTripleInputComparisonData C hC s t E g h k X Y Z)

noncomputable def equivalenceIndexedRightTransportData (u v w : s.data.group)
    (eu : g * h = u) (ev : h * k = v) (ew : u * k = w) (ew' : g * v = w) :
    IsoData C.toWeaklyPointedSuperfusionData
      (convolutionObj C hC s.data (convolutionObj C hC s.data X.obj Y.obj) Z.obj w).val
      (C.tensorObj (C.tensorObj (X.obj g).val (Y.obj h).val) (Z.obj k).val) :=
  ((((equivalenceNamedComparisonData C hC s t E w
    (pullbackIndexedTensorSpanObj C hC s u k w ew
      (pullbackIndexedTensorSpanObj C hC s g h u eu X Y) Z)).symm C.toWeaklyPointedSuperfusionData).trans
    C.toWeaklyPointedSuperfusionData
      ⟨E.data.forward.map ((twistedPullback C hC s).data.associatorHom X.obj Y.obj Z.obj)
          (equivalenceGaugePhi C hC s t E w),
        E.data.forward.map ((twistedPullback C hC s).data.associatorInv X.obj Y.obj Z.obj)
          (equivalenceGaugePhi C hC s t E w)⟩).trans C.toWeaklyPointedSuperfusionData
    (equivalenceIndexedRightComparisonData C hC s t E X.obj Y.obj Z.obj
      (equivalenceGaugePhi C hC s t E g) (equivalenceGaugePhi C hC s t E h)
      (equivalenceGaugePhi C hC s t E k) (equivalenceGaugePhi C hC s t E v)
      (equivalenceGaugePhi C hC s t E w)
      ((map_mul (equivalenceGaugePhi C hC s t E) h k).symm.trans
        (congrArg (equivalenceGaugePhi C hC s t E) ev))
      ((map_mul (equivalenceGaugePhi C hC s t E) g v).symm.trans
        (congrArg (equivalenceGaugePhi C hC s t E) ew')))).trans C.toWeaklyPointedSuperfusionData
      (equivalenceNamedTripleInputComparisonData C hC s t E g h k X Y Z)

end RMod.Classification
