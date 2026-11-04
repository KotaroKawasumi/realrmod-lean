import RMod.Classification.Abstract.TensorIntertwiner

/-!
# The specified isomorphism of a tensor-generator comparison

This Mathlib view uses the same two maps and the already proved inverse
identities. It makes ordinary isomorphism calculus available without
changing the separated comparison data.
-/

set_option autoImplicit false

namespace RMod.Classification.TensorIntertwiner

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}}
  {S T : SimpleObject C} {U V : SimpleObject D}
  {E : SpanSuperfunctor C D S.data.object U.data.object}
  {H : SpanSuperfunctor C D T.data.object V.data.object}
  {N : SpanSuperfunctor C D (simpleTensorRepresentative C S T).data.object
    (simpleTensorRepresentative D U V).data.object} {a : ZMod 2}

def toIso (t : TensorIntertwiner S T U V E H N a) :
    @CategoryTheory.Iso (LinearCategory D) _
      (N.data.obj (tensorSpanObject C S T)).obj
      (D.data.tensorObj (E.data.obj (spanGenerator C S.data.object)).obj
        (H.data.obj (spanGenerator C T.data.object)).obj) :=
  ⟨t.data.hom, t.data.inv, t.laws.hom_inv, t.laws.inv_hom⟩

end RMod.Classification.TensorIntertwiner
