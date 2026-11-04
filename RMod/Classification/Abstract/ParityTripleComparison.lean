import RMod.Classification.Abstract.TripleComparison

/-!
# Even triple comparisons to a common right-parity normal form

The normal form is (E X ⊗ (H Y ⊗ K Z)) ⊗ Pₐ. Keeping its actual
maps, instead of only their parity, makes scalar extraction sensitive
to the contraction and crossing conventions in the reference category.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  (S T R : SimpleObject A) (U V W : SimpleObject C)

structure ParityTripleComparisonData (p : PiData C.data) (a : ZMod 2)
    (E : SpanSuperfunctorData A C S.data.object U.data.object)
    (H : SpanSuperfunctorData A C T.data.object V.data.object)
    (K : SpanSuperfunctorData A C R.data.object W.data.object)
    (N : SpanSuperfunctorData A C
      (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
      (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object) where
  app : (X : HomogeneousSpanCategory A S.data.object) → (Y : HomogeneousSpanCategory A T.data.object) →
    (Z : HomogeneousSpanCategory A R.data.object) →
    IsoData C.data (N.obj (tripleSpanObj A S T R X Y Z)).obj
      (C.data.tensorObj (C.data.tensorObj (E.obj X).obj (C.data.tensorObj (H.obj Y).obj (K.obj Z).obj))
        (p.factor a))

structure ParityTripleComparisonLaws {p : PiData C.data} {a : ZMod 2}
    {E : SpanSuperfunctorData A C S.data.object U.data.object}
    {H : SpanSuperfunctorData A C T.data.object V.data.object}
    {K : SpanSuperfunctorData A C R.data.object W.data.object}
    {N : SpanSuperfunctorData A C
      (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
      (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object}
    (d : ParityTripleComparisonData S T R U V W p a E H K N) : Prop where
  iso : ∀ X Y Z, EvenIsoLaws C.data (d.app X Y Z)
  naturality : ∀ {X X' : HomogeneousSpanCategory A S.data.object}
    {Y Y' : HomogeneousSpanCategory A T.data.object} {Z Z' : HomogeneousSpanCategory A R.data.object}
    {b c e : ZMod 2} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z'),
    A.data.IsHomogeneous b f.hom → A.data.IsHomogeneous c g.hom → A.data.IsHomogeneous e h.hom →
    C.data.comp (N.map (tripleSpanHom A S T R f g h)).hom (d.app X' Y' Z').hom =
      C.data.comp (d.app X Y Z).hom (C.data.tensorHom
        (C.data.tensorHom (E.map f).hom (C.data.tensorHom (H.map g).hom (K.map h).hom))
        (C.data.id (p.factor a)))

structure ParityTripleComparison (p : Pi C.data)
    (E : SpanSuperfunctor A C S.data.object U.data.object)
    (H : SpanSuperfunctor A C T.data.object V.data.object)
    (K : SpanSuperfunctor A C R.data.object W.data.object)
    (N : SpanSuperfunctor A C
      (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
      (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object) (a : ZMod 2) where
  data : ParityTripleComparisonData S T R U V W p.data a E.data H.data K.data N.data
  laws : ParityTripleComparisonLaws S T R U V W data

end RMod.Classification
