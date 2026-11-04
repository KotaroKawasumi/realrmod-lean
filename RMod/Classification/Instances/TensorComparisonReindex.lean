import RMod.Classification.Abstract.TensorComparison
import RMod.Classification.Instances.SpanReindexFunctor
import RMod.Classification.Proofs.SimpleTensorCongruence

/-!
# Binary comparisons are unchanged by reindexing their generators

Evaluate the supplied comparison on the identity inclusions of the new
spans into the old ones. Tensor constituents change by their already
proved parity-orbit congruence. All underlying ambient maps are unchanged,
so the inverse, grading and naturality laws specialize directly.
-/

set_option autoImplicit false

namespace RMod.Classification.TensorComparison

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T : SimpleObject A} {U V : SimpleObject C}
  (S' T' : SimpleObject A) (U' V' : SimpleObject C)
  (hS : SameParityOrbit A.data S'.data.object S.data.object)
  (hT : SameParityOrbit A.data T'.data.object T.data.object)
  (hU : SameParityOrbit C.data U'.data.object U.data.object)
  (hV : SameParityOrbit C.data V'.data.object V.data.object)

noncomputable def reindexData
    {E : SpanSuperfunctorData A C S.data.object U.data.object}
    {H : SpanSuperfunctorData A C T.data.object V.data.object}
    {N : SpanSuperfunctorData A C (simpleTensorRepresentative A S T).data.object
      (simpleTensorRepresentative C U V).data.object}
    (d : TensorComparisonData S T U V E H N) :
    TensorComparisonData S' T' U' V'
      (spanReindexSuperfunctorData S U S' U' hS hU E)
      (spanReindexSuperfunctorData T V T' V' hT hV H)
      (spanReindexSuperfunctorData (simpleTensorRepresentative A S T) (simpleTensorRepresentative C U V)
        (simpleTensorRepresentative A S' T') (simpleTensorRepresentative C U' V')
        (simpleTensorRepresentative_congr A S' S T' T hS hT)
        (simpleTensorRepresentative_congr C U' U V' V hU hV) N) where
  app X Y := d.app
    ((spanChangeSuperequivalence A
      (inHomogeneousSpan_congr_generator A S'.laws.simple S.laws.simple hS)).forwardFunctor.data.obj X)
    ((spanChangeSuperequivalence A
      (inHomogeneousSpan_congr_generator A T'.laws.simple T.laws.simple hT)).forwardFunctor.data.obj Y)

variable {E : SpanSuperfunctor A C S.data.object U.data.object}
  {H : SpanSuperfunctor A C T.data.object V.data.object}
  {N : SpanSuperfunctor A C (simpleTensorRepresentative A S T).data.object
    (simpleTensorRepresentative C U V).data.object} {a : ZMod 2}

theorem reindexLaws (η : TensorComparison S T U V E H N a) :
    TensorComparisonLaws S' T' U' V' a (reindexData S' T' U' V' hS hT hU hV η.data) where
  iso _ _ := η.laws.iso _ _
  hom_grade _ _ := η.laws.hom_grade _ _
  inv_grade _ _ := η.laws.inv_grade _ _
  naturality f g hf hg := η.laws.naturality
    ((spanChangeSuperequivalence A
      (inHomogeneousSpan_congr_generator A S'.laws.simple S.laws.simple hS)).forwardFunctor.data.map f)
    ((spanChangeSuperequivalence A
      (inHomogeneousSpan_congr_generator A T'.laws.simple T.laws.simple hT)).forwardFunctor.data.map g) hf hg

noncomputable def reindex (η : TensorComparison S T U V E H N a) :
    TensorComparison S' T' U' V'
      (spanReindexSuperfunctor S U S' U' hS hU E)
      (spanReindexSuperfunctor T V T' V' hT hV H)
      (spanReindexSuperfunctor (simpleTensorRepresentative A S T) (simpleTensorRepresentative C U V)
        (simpleTensorRepresentative A S' T') (simpleTensorRepresentative C U' V')
        (simpleTensorRepresentative_congr A S' S T' T hS hT)
        (simpleTensorRepresentative_congr C U' U V' V hU hV) N) a :=
  ⟨reindexData S' T' U' V' hS hT hU hV η.data, reindexLaws S' T' U' V' hS hT hU hV η⟩

end RMod.Classification.TensorComparison
