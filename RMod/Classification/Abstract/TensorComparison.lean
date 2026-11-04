import RMod.Classification.Abstract.TensorIntertwiner
import RMod.Classification.Instances.SpanTensor

/-!
# Homogeneous natural comparisons between two multiplication operations

At each pair of objects, data retain both comparison maps. Laws assert
their inverse identities, common degree, and signed naturality against
all pairs of homogeneous morphisms. The complete structure uses complete
component functors and complete ambient categories.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}}
  (S T : SimpleObject C) (U V : SimpleObject D)

structure TensorComparisonData
    (E : SpanSuperfunctorData C D S.data.object U.data.object)
    (H : SpanSuperfunctorData C D T.data.object V.data.object)
    (N : SpanSuperfunctorData C D (simpleTensorRepresentative C S T).data.object
      (simpleTensorRepresentative D U V).data.object) where
  app : (X : HomogeneousSpanCategory C S.data.object) →
    (Y : HomogeneousSpanCategory C T.data.object) →
    IsoData D.data (N.obj (spanTensorObj C S T X Y)).obj
      (D.data.tensorObj (E.obj X).obj (H.obj Y).obj)

structure TensorComparisonLaws
    {E : SpanSuperfunctorData C D S.data.object U.data.object}
    {H : SpanSuperfunctorData C D T.data.object V.data.object}
    {N : SpanSuperfunctorData C D (simpleTensorRepresentative C S T).data.object
      (simpleTensorRepresentative D U V).data.object}
    (a : ZMod 2) (d : TensorComparisonData S T U V E H N) : Prop where
  iso : ∀ X Y, IsoLaws D.data (d.app X Y)
  hom_grade : ∀ X Y, D.data.IsHomogeneous a (d.app X Y).hom
  inv_grade : ∀ X Y, D.data.IsHomogeneous a (d.app X Y).inv
  naturality : ∀ {X X' : HomogeneousSpanCategory C S.data.object}
    {Y Y' : HomogeneousSpanCategory C T.data.object} {b c : ZMod 2}
    (f : X ⟶ X') (g : Y ⟶ Y'),
    C.data.IsHomogeneous b f.hom → C.data.IsHomogeneous c g.hom →
    D.data.comp (N.map (spanTensorHom C S T f g)).hom (d.app X' Y').hom =
      D.data.smul ((-1 : ℝ) ^ (a * (b + c)).val)
        (D.data.comp (d.app X Y).hom (D.data.tensorHom (E.map f).hom (H.map g).hom))

structure TensorComparison
    (E : SpanSuperfunctor C D S.data.object U.data.object)
    (H : SpanSuperfunctor C D T.data.object V.data.object)
    (N : SpanSuperfunctor C D (simpleTensorRepresentative C S T).data.object
      (simpleTensorRepresentative D U V).data.object) (a : ZMod 2) where
  data : TensorComparisonData S T U V E.data H.data N.data
  laws : TensorComparisonLaws S T U V a data

end RMod.Classification
