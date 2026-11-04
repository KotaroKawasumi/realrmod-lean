import RMod.Classification.Abstract.SpanSuperfunctor
import RMod.Classification.Abstract.Normalizers
import RMod.Classification.Instances.SpanGenerator
import RMod.Classification.Instances.TensorSpanObject

/-!
# Signed comparison of the two tensor actions at simple generators

The comparison and its inverse are existing isomorphism data. Their
degree, inverse identities, and the signed equation for every pair of
homogeneous endomorphisms are separate laws. All functors in the
completed structure have completed source and target categories.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}}
  (S T : SimpleObject C) (U V : SimpleObject D)

abbrev TensorIntertwinerData
    (E : SpanSuperfunctorData C D S.data.object U.data.object)
    (H : SpanSuperfunctorData C D T.data.object V.data.object)
    (M : SpanSuperfunctorData C D (simpleTensorRepresentative C S T).data.object
      (simpleTensorRepresentative D U V).data.object) :=
  IsoData D.data (M.obj (tensorSpanObject C S T)).obj
    (D.data.tensorObj (E.obj (spanGenerator C S.data.object)).obj
      (H.obj (spanGenerator C T.data.object)).obj)

structure TensorIntertwinerLaws
    {E : SpanSuperfunctorData C D S.data.object U.data.object}
    {H : SpanSuperfunctorData C D T.data.object V.data.object}
    {M : SpanSuperfunctorData C D (simpleTensorRepresentative C S T).data.object
      (simpleTensorRepresentative D U V).data.object}
    (a : ZMod 2) (d : TensorIntertwinerData S T U V E H M) : Prop
    extends IsoLaws D.data d where
  hom_grade : D.data.IsHomogeneous a d.hom
  inv_grade : D.data.IsHomogeneous a d.inv
  intertwines : ∀ {b c : ZMod 2}
    (f : spanGenerator C S.data.object ⟶ spanGenerator C S.data.object)
    (g : spanGenerator C T.data.object ⟶ spanGenerator C T.data.object),
    C.data.IsHomogeneous b f.hom → C.data.IsHomogeneous c g.hom →
    D.data.comp (M.map (ObjectProperty.homMk (C.data.tensorHom f.hom g.hom) :
      tensorSpanObject C S T ⟶ tensorSpanObject C S T)).hom d.hom =
      D.data.smul ((-1 : ℝ) ^ (a * (b + c)).val)
        (D.data.comp d.hom (D.data.tensorHom (E.map f).hom (H.map g).hom))

structure TensorIntertwiner
    (E : SpanSuperfunctor C D S.data.object U.data.object)
    (H : SpanSuperfunctor C D T.data.object V.data.object)
    (M : SpanSuperfunctor C D (simpleTensorRepresentative C S T).data.object
      (simpleTensorRepresentative D U V).data.object) (a : ZMod 2) where
  data : TensorIntertwinerData S T U V E.data H.data M.data
  laws : TensorIntertwinerLaws S T U V a data

end RMod.Classification
