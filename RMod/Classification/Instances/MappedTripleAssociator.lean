import RMod.Classification.Instances.TripleRightFunctor
import RMod.Classification.Instances.SpanMapIso

/-!
# The mapped associator after identifying the product component functors

First use the given equality of complete functors on the left triple
span, then apply the right product functor to the source associator.
The equality map is explicit, so no coherence assumption is hidden in
an identification of the two differently bracketed group products.
-/

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

noncomputable def mappedTripleAssociatorData (e : tripleRightFunctor S T R U V W N = M)
    (X : HomogeneousSpanCategory A S.data.object) (Y : HomogeneousSpanCategory A T.data.object)
    (Z : HomogeneousSpanCategory A R.data.object) :
    IsoData C.data (M.data.obj (tripleSpanObj A S T R X Y Z)).obj
      (N.data.obj (rightTripleSpanObj A S T R X Y Z)).obj :=
  (IsoData.ofEq C.data (congrArg
    (fun Q => (Q.data.obj (tripleSpanObj A S T R X Y Z)).obj) e.symm)).trans C.data
      (SpanSuperfunctor.mapIsoData N.data
        (X := tripleSpanObjInRight A S T R X Y Z) (Y := rightTripleSpanObj A S T R X Y Z)
        (IsoData.assoc A.data X.obj Y.obj Z.obj))

end RMod.Classification
