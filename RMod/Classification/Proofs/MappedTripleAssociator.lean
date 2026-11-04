import RMod.Classification.Instances.MappedTripleAssociator
import RMod.Classification.Proofs.IsoCalculus

/-! # The mapped comparison after functor equality is an even isomorphism -/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  (S T R : SimpleObject A) (U V W : SimpleObject C)
  (N : SpanSuperfunctor A C
    (simpleTensorRepresentative A S (simpleTensorRepresentative A T R)).data.object
    (simpleTensorRepresentative C U (simpleTensorRepresentative C V W)).data.object)
  (M : SpanSuperfunctor A C
    (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
    (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object)

theorem mappedTripleAssociator_evenIso (e : tripleRightFunctor S T R U V W N = M)
    (X : HomogeneousSpanCategory A S.data.object) (Y : HomogeneousSpanCategory A T.data.object)
    (Z : HomogeneousSpanCategory A R.data.object) :
    EvenIsoLaws C.data (mappedTripleAssociatorData S T R U V W N M e X Y Z) :=
  (EvenIsoLaws.ofEq C.laws _).trans C.laws (N.mapEvenIsoLaws
    (X := tripleSpanObjInRight A S T R X Y Z) (Y := rightTripleSpanObj A S T R X Y Z)
    (EvenIsoLaws.assoc A.laws X.obj Y.obj Z.obj))

end RMod.Classification
