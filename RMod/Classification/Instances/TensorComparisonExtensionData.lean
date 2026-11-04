import RMod.Classification.Abstract.TensorComparison
import RMod.Classification.Instances.HomogeneousSpanPresentation
import RMod.Classification.Instances.HomogeneousSumTensorData
import RMod.Classification.Instances.HomogeneousSumComparisonData
import RMod.Classification.Instances.SpanHomogeneousSumMap

/-!
# Objectwise matrix extension of a tensor-generator comparison

Tensor the canonical presentations in both source components. One
presentation is mapped by the product-component functor; the other is
formed by tensoring the two individual functor images. Their parity
lists agree literally. The signed homogeneous comparison formula then
supplies both maps at every pair of objects.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {C D : WeaklyPointedSuperfusion.{0, 0}}
  (S T : SimpleObject C) (U V : SimpleObject D)

noncomputable def tensorComparisonSourceData
    (N : SpanSuperfunctorData C D (simpleTensorRepresentative C S T).data.object
      (simpleTensorRepresentative D U V).data.object)
    (X : HomogeneousSpanCategory C S.data.object) (Y : HomogeneousSpanCategory C T.data.object) :
    HomogeneousSumData D.data (N.obj (tensorSpanObject C S T)).obj
      (N.obj (spanTensorObj C S T X Y)).obj (spanSize X * spanSize Y) :=
  spanHomogeneousSumMapData (X := tensorSpanObject C S T) (Y := spanTensorObj C S T X Y) N
    (HomogeneousSum.tensorData (spanPresentation X).data (spanPresentation Y).data)

noncomputable def tensorComparisonTargetData
    (E : SpanSuperfunctorData C D S.data.object U.data.object)
    (H : SpanSuperfunctorData C D T.data.object V.data.object)
    (X : HomogeneousSpanCategory C S.data.object) (Y : HomogeneousSpanCategory C T.data.object) :
    HomogeneousSumData D.data
      (D.data.tensorObj (E.obj (spanGenerator C S.data.object)).obj (H.obj (spanGenerator C T.data.object)).obj)
      (D.data.tensorObj (E.obj X).obj (H.obj Y).obj) (spanSize X * spanSize Y) :=
  HomogeneousSum.tensorData
    (spanHomogeneousSumMapData (X := spanGenerator C S.data.object) (Y := X) E (spanPresentation X).data)
    (spanHomogeneousSumMapData (X := spanGenerator C T.data.object) (Y := Y) H (spanPresentation Y).data)

noncomputable def tensorComparisonExtensionData
    (E : SpanSuperfunctorData C D S.data.object U.data.object)
    (H : SpanSuperfunctorData C D T.data.object V.data.object)
    (N : SpanSuperfunctorData C D (simpleTensorRepresentative C S T).data.object
      (simpleTensorRepresentative D U V).data.object)
    (a : ZMod 2) (t : TensorIntertwinerData S T U V E H N) :
    TensorComparisonData S T U V E H N where
  app X Y := HomogeneousSum.comparisonIsoData a
    (tensorComparisonSourceData S T U V N X Y) (tensorComparisonTargetData S T U V E H X Y) t

end RMod.Classification
