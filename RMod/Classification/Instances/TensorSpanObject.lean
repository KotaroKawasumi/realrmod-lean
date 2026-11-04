import RMod.Classification.Abstract.HomogeneousSpan
import RMod.Classification.Proofs.SimpleTensorCongruence

/-!
# A tensor-product generator as an object of its product component

The actual tensor product belongs to the span of the simple constituent
chosen for intrinsic multiplication. Its membership is the homogeneous
sum presentation proved from tensor isotypy.
-/

set_option autoImplicit false

namespace RMod.Classification

def tensorSpanObject (C : WeaklyPointedSuperfusion.{0, 0}) (S T : SimpleObject C) :
    HomogeneousSpanCategory C (simpleTensorRepresentative C S T).data.object :=
  ⟨C.data.tensorObj S.data.object T.data.object, _, tensorRepresentative_homogeneousSum C S T⟩

end RMod.Classification
