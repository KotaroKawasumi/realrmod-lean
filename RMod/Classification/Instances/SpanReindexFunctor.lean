import RMod.Classification.Instances.SpanChange
import RMod.Classification.Instances.SpanSuperfunctorComposition
import RMod.Classification.Instances.SpanSuperequivalence
import RMod.Classification.Abstract.SimpleObjects

/-!
# Reindexing a component functor by equivalent simple generators

Identity changes of full span present a given functor on new generators
in the same parity orbits. These operations preserve its ambient object
and morphism maps. The separate laws are the composition laws of the
completed component functors.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  (S : SimpleObject A) (T : SimpleObject C) (U : SimpleObject A) (V : SimpleObject C)
  (hS : SameParityOrbit A.data U.data.object S.data.object)
  (hT : SameParityOrbit C.data V.data.object T.data.object)

def spanReindexSuperfunctorData (F : SpanSuperfunctorData A C S.data.object T.data.object) :
    SpanSuperfunctorData A C U.data.object V.data.object :=
  SpanSuperfunctor.compData
    (SpanSuperfunctor.compData
      (spanChangeSuperequivalence A
        (inHomogeneousSpan_congr_generator A U.laws.simple S.laws.simple hS)).forwardFunctor.data F)
    (spanChangeSuperequivalence C
      (inHomogeneousSpan_congr_generator C T.laws.simple V.laws.simple hT.symm)).forwardFunctor.data

theorem spanReindexSuperfunctorLaws (F : SpanSuperfunctor A C S.data.object T.data.object) :
    SpanSuperfunctorLaws A C U.data.object V.data.object (spanReindexSuperfunctorData S T U V hS hT F.data) :=
  SpanSuperfunctor.compLaws
    ((spanChangeSuperequivalence A
      (inHomogeneousSpan_congr_generator A U.laws.simple S.laws.simple hS)).forwardFunctor.comp F)
    (spanChangeSuperequivalence C
      (inHomogeneousSpan_congr_generator C T.laws.simple V.laws.simple hT.symm)).forwardFunctor

def spanReindexSuperfunctor (F : SpanSuperfunctor A C S.data.object T.data.object) :
    SpanSuperfunctor A C U.data.object V.data.object :=
  ⟨spanReindexSuperfunctorData S T U V hS hT F.data, spanReindexSuperfunctorLaws S T U V hS hT F⟩

end RMod.Classification
