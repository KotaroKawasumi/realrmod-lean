import RMod.Classification.Instances.TripleSpan
import RMod.Classification.Instances.SpanChange
import RMod.Classification.Instances.SpanSuperequivalence
import RMod.Classification.Proofs.SimpleTensorAssociativity

/-!
# The two associated tensor components have identical full spans

Associativity of the intrinsic simple orbit product was proved using the
actual associator. The identity change of full span therefore compares
the two component presentations without changing any ambient object or
morphism. Both bracketed tensor objects are retained explicitly.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A : WeaklyPointedSuperfusion.{0, 0}) (S T R : SimpleObject A)

noncomputable def tripleAssociatorSpanEquivalence :
    SpanSuperequivalence A A (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
      (simpleTensorRepresentative A S (simpleTensorRepresentative A T R)).data.object :=
  spanChangeSuperequivalence A (inHomogeneousSpan_congr_generator A
    (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).laws.simple
    (simpleTensorRepresentative A S (simpleTensorRepresentative A T R)).laws.simple
    (simpleTensorRepresentative_assoc A S T R))

def rightTripleSpanObj (X : HomogeneousSpanCategory A S.data.object)
    (Y : HomogeneousSpanCategory A T.data.object) (Z : HomogeneousSpanCategory A R.data.object) :
    HomogeneousSpanCategory A (simpleTensorRepresentative A S (simpleTensorRepresentative A T R)).data.object :=
  ⟨A.data.tensorObj X.obj (A.data.tensorObj Y.obj Z.obj),
    (spanTensorObj A S (simpleTensorRepresentative A T R) X (spanTensorObj A T R Y Z)).property⟩

def tripleSpanObjInRight (X : HomogeneousSpanCategory A S.data.object)
    (Y : HomogeneousSpanCategory A T.data.object) (Z : HomogeneousSpanCategory A R.data.object) :
    HomogeneousSpanCategory A (simpleTensorRepresentative A S (simpleTensorRepresentative A T R)).data.object :=
  ⟨A.data.tensorObj (A.data.tensorObj X.obj Y.obj) Z.obj,
    ((tripleAssociatorSpanEquivalence A S T R).forwardFunctor.data.obj (tripleSpanObj A S T R X Y Z)).property⟩

end RMod.Classification
