import RMod.Classification.Proofs.ParityTensoratorAssociativity
import RMod.Classification.Proofs.MappedTripleAssociator

/-!
# Tensorator associativity with identified product functors

The product at (gh)k and the product at g(hk) are the same selected
component after the group equality. This lemma retains the induced
object equality map inside the mapped source associator.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T R : SimpleObject A} {U V W : SimpleObject C} {p : Pi C.data} {a b c d : ZMod 2}
  {E : SpanSuperfunctor A C S.data.object U.data.object}
  {H : SpanSuperfunctor A C T.data.object V.data.object}
  {K : SpanSuperfunctor A C R.data.object W.data.object}
  {F : SpanSuperfunctor A C (simpleTensorRepresentative A S T).data.object
    (simpleTensorRepresentative C U V).data.object}
  {J : SpanSuperfunctor A C (simpleTensorRepresentative A T R).data.object
    (simpleTensorRepresentative C V W).data.object}
  {N : SpanSuperfunctor A C
    (simpleTensorRepresentative A S (simpleTensorRepresentative A T R)).data.object
    (simpleTensorRepresentative C U (simpleTensorRepresentative C V W)).data.object}
  {M : SpanSuperfunctor A C
    (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
    (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object}
  (ηL : ParityTensorComparison S T U V p E H F a)
  (θL : ParityTensorComparison (simpleTensorRepresentative A S T) R
    (simpleTensorRepresentative C U V) W p F K M b)
  (ηR : ParityTensorComparison T R V W p H K J c)
  (θR : ParityTensorComparison S (simpleTensorRepresentative A T R) U
    (simpleTensorRepresentative C V W) p E J N d)

theorem parityTensorator_associativity_of_functor_eq (hN : tripleRightFunctor S T R U V W N = M)
    (e : a + b = c + d) (ω : ℝˣ)
    (X : HomogeneousSpanCategory A S.data.object) (Y : HomogeneousSpanCategory A T.data.object)
    (Z : HomogeneousSpanCategory A R.data.object)
    (heq : ((Eq.mp (congrArg (fun Q => ParityTripleComparison S T R U V W p E H K Q (c + d)) hN)
      (parityTripleRight ηR θR)).data.app X Y Z).hom = C.data.smul (ω : ℝ)
      ((parityTripleTransport e (parityTripleLeft ηL θL)).data.app X Y Z).hom) :
    C.data.comp (parityTripleLeftTensorator S T R U V W ηL.data θL.data X Y Z).hom
      (mappedTripleAssociatorData S T R U V W N M hN X Y Z).hom =
      C.data.comp (p.data.localAssociator (E.data.obj X).obj (H.data.obj Y).obj (K.data.obj Z).obj
        a b c d e ω).hom (parityTripleRightTensorator S T R U V W ηR.data θR.data X Y Z).hom := by
  subst M
  have h := parityTensorator_associativity ηL θL ηR θR e ω X Y Z heq
  simpa only [mappedTripleAssociatorData, IsoData.ofEq, IsoData.refl, IsoData.trans,
    C.laws.id_comp] using h

end RMod.Classification
