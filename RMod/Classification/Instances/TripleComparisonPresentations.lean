import RMod.Classification.Instances.TripleComparisonEvaluation
import RMod.Classification.Instances.HomogeneousSumTensor
import RMod.Classification.Instances.SpanHomogeneousSumMap
import RMod.Classification.Instances.HomogeneousSpanPresentation

/-!
# Mapped presentations of triple tensor products

The nested tensor presentation retains all homogeneous inclusions and
projections. Mapping it through the product component functor gives a
complete family of tests for maps out of every triple tensor object.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  (S T R : SimpleObject A) (U V W : SimpleObject C)

noncomputable def tripleComparisonSourcePresentation
    (N : SpanSuperfunctor A C
      (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
      (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object)
    (X : HomogeneousSpanCategory A S.data.object) (Y : HomogeneousSpanCategory A T.data.object)
    (Z : HomogeneousSpanCategory A R.data.object) :
    HomogeneousSum C.data (N.data.obj (tripleSpanGenerator A S T R)).obj
      (N.data.obj (tripleSpanObj A S T R X Y Z)).obj ((spanSize X * spanSize Y) * spanSize Z) :=
  spanHomogeneousSumMap (X := tripleSpanGenerator A S T R) (Y := tripleSpanObj A S T R X Y Z) N
    (((spanPresentation X).tensor (spanPresentation Y)).tensor (spanPresentation Z))

end RMod.Classification
