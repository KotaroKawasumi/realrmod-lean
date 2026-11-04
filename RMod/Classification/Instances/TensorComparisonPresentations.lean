import RMod.Classification.Instances.TensorComparisonExtensionData
import RMod.Classification.Instances.HomogeneousSumTensor

/-!
# The two completed presentations used in tensor comparison

The product functor maps the source tensor presentation. The target
presentation is the tensor of the two individually mapped presentations.
The map and tensor constructors already prove all of their laws.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {C D : WeaklyPointedSuperfusion.{0, 0}}
  (S T : SimpleObject C) (U V : SimpleObject D)

noncomputable def tensorComparisonSourcePresentation
    (N : SpanSuperfunctor C D (simpleTensorRepresentative C S T).data.object
      (simpleTensorRepresentative D U V).data.object)
    (X : HomogeneousSpanCategory C S.data.object) (Y : HomogeneousSpanCategory C T.data.object) :
    HomogeneousSum D.data (N.data.obj (tensorSpanObject C S T)).obj
      (N.data.obj (spanTensorObj C S T X Y)).obj (spanSize X * spanSize Y) :=
  spanHomogeneousSumMap (X := tensorSpanObject C S T) (Y := spanTensorObj C S T X Y) N
    ((spanPresentation X).tensor (spanPresentation Y))

noncomputable def tensorComparisonTargetPresentation
    (E : SpanSuperfunctor C D S.data.object U.data.object)
    (H : SpanSuperfunctor C D T.data.object V.data.object)
    (X : HomogeneousSpanCategory C S.data.object) (Y : HomogeneousSpanCategory C T.data.object) :
    HomogeneousSum D.data
      (D.data.tensorObj (E.data.obj (spanGenerator C S.data.object)).obj (H.data.obj (spanGenerator C T.data.object)).obj)
      (D.data.tensorObj (E.data.obj X).obj (H.data.obj Y).obj) (spanSize X * spanSize Y) :=
  (spanHomogeneousSumMap (X := spanGenerator C S.data.object) (Y := X) E (spanPresentation X)).tensor
    (spanHomogeneousSumMap (X := spanGenerator C T.data.object) (Y := Y) H (spanPresentation Y))

end RMod.Classification
