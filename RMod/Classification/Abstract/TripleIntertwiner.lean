import RMod.Classification.Abstract.TensorIntertwiner
import RMod.Classification.Abstract.HomogeneousIso
import RMod.Classification.Instances.TripleSpan

/-!
# Homogeneous comparison of three tensor actions

The comparison data retain an isomorphism from the product-component
functor to the triple of the three generator images. Laws assert its
degree and signed naturality against three independent homogeneous
endomorphisms. All component functors in the completed comparison act
between completed ambient categories.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  (S T R : SimpleObject A) (U V W : SimpleObject C)

abbrev TripleIntertwinerData
    (E : SpanSuperfunctorData A C S.data.object U.data.object)
    (H : SpanSuperfunctorData A C T.data.object V.data.object)
    (K : SpanSuperfunctorData A C R.data.object W.data.object)
    (N : SpanSuperfunctorData A C
      (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
      (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object) :=
  IsoData C.data (N.obj (tripleSpanGenerator A S T R)).obj
    (C.data.tensorObj
      (C.data.tensorObj (E.obj (spanGenerator A S.data.object)).obj (H.obj (spanGenerator A T.data.object)).obj)
      (K.obj (spanGenerator A R.data.object)).obj)

structure TripleIntertwinerLaws
    {E : SpanSuperfunctorData A C S.data.object U.data.object}
    {H : SpanSuperfunctorData A C T.data.object V.data.object}
    {K : SpanSuperfunctorData A C R.data.object W.data.object}
    {N : SpanSuperfunctorData A C
      (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
      (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object}
    (a : ZMod 2) (d : TripleIntertwinerData S T R U V W E H K N) : Prop
    extends HomogeneousIsoLaws C.data a d where
  intertwines : ∀ {b c e : ZMod 2}
    (f : spanGenerator A S.data.object ⟶ spanGenerator A S.data.object)
    (g : spanGenerator A T.data.object ⟶ spanGenerator A T.data.object)
    (h : spanGenerator A R.data.object ⟶ spanGenerator A R.data.object),
    A.data.IsHomogeneous b f.hom → A.data.IsHomogeneous c g.hom → A.data.IsHomogeneous e h.hom →
    C.data.comp (N.map (tripleSpanHom A S T R f g h)).hom d.hom =
      C.data.smul ((-1 : ℝ) ^ (a * ((b + c) + e)).val)
        (C.data.comp d.hom (C.data.tensorHom (C.data.tensorHom (E.map f).hom (H.map g).hom) (K.map h).hom))

structure TripleIntertwiner
    (E : SpanSuperfunctor A C S.data.object U.data.object)
    (H : SpanSuperfunctor A C T.data.object V.data.object)
    (K : SpanSuperfunctor A C R.data.object W.data.object)
    (N : SpanSuperfunctor A C
      (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
      (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object) (a : ZMod 2) where
  data : TripleIntertwinerData S T R U V W E.data H.data K.data N.data
  laws : TripleIntertwinerLaws S T R U V W a data

end RMod.Classification
