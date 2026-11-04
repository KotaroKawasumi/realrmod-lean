import RMod.Classification.Abstract.TripleIntertwiner

/-! # Mathlib's isomorphism view of a specified triple comparison -/

set_option autoImplicit false

namespace RMod.Classification.TripleIntertwiner

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T R : SimpleObject A} {U V W : SimpleObject C}
  {E : SpanSuperfunctor A C S.data.object U.data.object}
  {H : SpanSuperfunctor A C T.data.object V.data.object}
  {K : SpanSuperfunctor A C R.data.object W.data.object}
  {N : SpanSuperfunctor A C
    (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
    (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object} {a : ZMod 2}

def toIso (t : TripleIntertwiner S T R U V W E H K N a) :
    @CategoryTheory.Iso (LinearCategory C) _ (N.data.obj (tripleSpanGenerator A S T R)).obj
      (C.data.tensorObj
        (C.data.tensorObj (E.data.obj (spanGenerator A S.data.object)).obj (H.data.obj (spanGenerator A T.data.object)).obj)
        (K.data.obj (spanGenerator A R.data.object)).obj) :=
  ⟨t.data.hom, t.data.inv, t.laws.hom_inv, t.laws.inv_hom⟩

end RMod.Classification.TripleIntertwiner
