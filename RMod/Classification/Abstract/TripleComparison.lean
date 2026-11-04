import RMod.Classification.Abstract.TripleIntertwiner

/-!
# Homogeneous natural comparison of three component tensor operations

Both comparison maps are specified on every triple of objects. The laws
retain their homogeneous inverse identities and signed naturality on
arbitrary homogeneous triples of morphisms, not only endomorphisms of
the generators. The completed structure uses completed component functors.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  (S T R : SimpleObject A) (U V W : SimpleObject C)

structure TripleComparisonData
    (E : SpanSuperfunctorData A C S.data.object U.data.object)
    (H : SpanSuperfunctorData A C T.data.object V.data.object)
    (K : SpanSuperfunctorData A C R.data.object W.data.object)
    (N : SpanSuperfunctorData A C
      (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
      (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object) where
  app : (X : HomogeneousSpanCategory A S.data.object) → (Y : HomogeneousSpanCategory A T.data.object) →
    (Z : HomogeneousSpanCategory A R.data.object) →
    IsoData C.data (N.obj (tripleSpanObj A S T R X Y Z)).obj
      (C.data.tensorObj (C.data.tensorObj (E.obj X).obj (H.obj Y).obj) (K.obj Z).obj)

structure TripleComparisonLaws
    {E : SpanSuperfunctorData A C S.data.object U.data.object}
    {H : SpanSuperfunctorData A C T.data.object V.data.object}
    {K : SpanSuperfunctorData A C R.data.object W.data.object}
    {N : SpanSuperfunctorData A C
      (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
      (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object}
    (a : ZMod 2) (d : TripleComparisonData S T R U V W E H K N) : Prop where
  iso : ∀ X Y Z, HomogeneousIsoLaws C.data a (d.app X Y Z)
  naturality : ∀ {X X' : HomogeneousSpanCategory A S.data.object}
    {Y Y' : HomogeneousSpanCategory A T.data.object} {Z Z' : HomogeneousSpanCategory A R.data.object}
    {b c e : ZMod 2} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z'),
    A.data.IsHomogeneous b f.hom → A.data.IsHomogeneous c g.hom → A.data.IsHomogeneous e h.hom →
    C.data.comp (N.map (tripleSpanHom A S T R f g h)).hom (d.app X' Y' Z').hom =
      C.data.smul ((-1 : ℝ) ^ (a * ((b + c) + e)).val)
        (C.data.comp (d.app X Y Z).hom
          (C.data.tensorHom (C.data.tensorHom (E.map f).hom (H.map g).hom) (K.map h).hom))

structure TripleComparison
    (E : SpanSuperfunctor A C S.data.object U.data.object)
    (H : SpanSuperfunctor A C T.data.object V.data.object)
    (K : SpanSuperfunctor A C R.data.object W.data.object)
    (N : SpanSuperfunctor A C
      (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
      (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object) (a : ZMod 2) where
  data : TripleComparisonData S T R U V W E.data H.data K.data N.data
  laws : TripleComparisonLaws S T R U V W a data

end RMod.Classification
