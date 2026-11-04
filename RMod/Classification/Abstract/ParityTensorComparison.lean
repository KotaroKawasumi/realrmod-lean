import RMod.Classification.Abstract.TensorComparison

/-!
# Even multiplication comparison with the specified right parity factor

The maps have the orientation of the reconstruction tensorator:
(E X ⊗ H Y) ⊗ Pₐ → N (X ⊗ Y). Laws concern precisely those
maps and their inverses. The complete comparison uses complete component
functors and a complete parity object.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  (S T : SimpleObject A) (U V : SimpleObject C)

structure ParityTensorComparisonData (p : PiData C.data) (a : ZMod 2)
    (E : SpanSuperfunctorData A C S.data.object U.data.object)
    (H : SpanSuperfunctorData A C T.data.object V.data.object)
    (N : SpanSuperfunctorData A C (simpleTensorRepresentative A S T).data.object
      (simpleTensorRepresentative C U V).data.object) where
  app : (X : HomogeneousSpanCategory A S.data.object) →
    (Y : HomogeneousSpanCategory A T.data.object) →
    IsoData C.data (C.data.tensorObj (C.data.tensorObj (E.obj X).obj (H.obj Y).obj) (p.factor a))
      (N.obj (spanTensorObj A S T X Y)).obj

structure ParityTensorComparisonLaws {p : PiData C.data} {a : ZMod 2}
    {E : SpanSuperfunctorData A C S.data.object U.data.object}
    {H : SpanSuperfunctorData A C T.data.object V.data.object}
    {N : SpanSuperfunctorData A C (simpleTensorRepresentative A S T).data.object
      (simpleTensorRepresentative C U V).data.object}
    (d : ParityTensorComparisonData S T U V p a E H N) : Prop where
  iso : ∀ X Y, EvenIsoLaws C.data (d.app X Y)
  naturality : ∀ {X X' : HomogeneousSpanCategory A S.data.object}
    {Y Y' : HomogeneousSpanCategory A T.data.object} {b c : ZMod 2}
    (f : X ⟶ X') (g : Y ⟶ Y'),
    A.data.IsHomogeneous b f.hom → A.data.IsHomogeneous c g.hom →
    C.data.comp (C.data.tensorHom (C.data.tensorHom (E.map f).hom (H.map g).hom)
      (C.data.id (p.factor a))) (d.app X' Y').hom =
      C.data.comp (d.app X Y).hom (N.map (spanTensorHom A S T f g)).hom

structure ParityTensorComparison (p : Pi C.data)
    (E : SpanSuperfunctor A C S.data.object U.data.object)
    (H : SpanSuperfunctor A C T.data.object V.data.object)
    (N : SpanSuperfunctor A C (simpleTensorRepresentative A S T).data.object
      (simpleTensorRepresentative C U V).data.object) (a : ZMod 2) where
  data : ParityTensorComparisonData S T U V p.data a E.data H.data N.data
  laws : ParityTensorComparisonLaws S T U V data

end RMod.Classification
