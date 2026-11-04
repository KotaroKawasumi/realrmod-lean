import RMod.Classification.Instances.SpanGenerator
import RMod.Classification.Instances.TensorSimpleRetract
import RMod.Classification.Instances.TensorSpanObject
import RMod.Classification.Instances.SpanEndSuperEquivalence
import RMod.Classification.Proofs.TensorEndComparison
import RMod.Classification.Proofs.SpanComparisonRealization
import RMod.Classification.Proofs.SpanSimpleImages
import RMod.Classification.Proofs.SpanSuperequivalence

/-!
# A component equivalence realizing the tensor action of two given functors

Tensor the two specified generator algebra maps, transport the product's
simple retract, and realize the resulting ambient algebra map by a
component equivalence. Its value on the tensor-product generator has a
specified even comparison with the tensor product of the two functor
values, intertwining every tensor of source endomorphisms.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

theorem exists_tensorGeneratorComparison (C D : PiSuperfusion.{0, 0})
    (S T : SimpleObject C.toWeaklyPointedSuperfusion) {U V : D.data.Obj}
    (E : SpanSuperequivalence C.toWeaklyPointedSuperfusion D.toWeaklyPointedSuperfusion S.data.object U)
    (H : SpanSuperequivalence C.toWeaklyPointedSuperfusion D.toWeaklyPointedSuperfusion T.data.object V) :
    ∃ (R : SimpleObject D.toWeaklyPointedSuperfusion)
      (M : SpanSuperequivalence C.toWeaklyPointedSuperfusion D.toWeaklyPointedSuperfusion
        (simpleTensorRepresentative C.toWeaklyPointedSuperfusion S T).data.object R.data.object)
      (e : IsoData D.data.toWeaklyPointedSuperfusionData
        (M.forwardFunctor.data.obj (tensorSpanObject C.toWeaklyPointedSuperfusion S T)).obj
        (D.data.tensorObj
          (E.forwardFunctor.data.obj (spanGenerator C.toWeaklyPointedSuperfusion S.data.object)).obj
          (H.forwardFunctor.data.obj (spanGenerator C.toWeaklyPointedSuperfusion T.data.object)).obj)),
      EvenIsoLaws D.data.toWeaklyPointedSuperfusionData e ∧
      ∀ (f : @End (LinearCategory C.toWeaklyPointedSuperfusion) _ S.data.object)
        (g : @End (LinearCategory C.toWeaklyPointedSuperfusion) _ T.data.object),
        D.data.comp (M.forwardFunctor.data.map (ObjectProperty.homMk (C.data.tensorHom f g) :
          tensorSpanObject C.toWeaklyPointedSuperfusion S T ⟶
            tensorSpanObject C.toWeaklyPointedSuperfusion S T)).hom e.hom =
        D.data.comp e.hom (D.data.tensorHom
          (E.forwardFunctor.data.map (ObjectProperty.homMk f : spanGenerator C.toWeaklyPointedSuperfusion S.data.object ⟶
            spanGenerator C.toWeaklyPointedSuperfusion S.data.object)).hom
          (H.forwardFunctor.data.map (ObjectProperty.homMk g : spanGenerator C.toWeaklyPointedSuperfusion T.data.object ⟶
            spanGenerator C.toWeaklyPointedSuperfusion T.data.object)).hom) := by
  let X := (E.forwardFunctor.data.obj (spanGenerator C.toWeaklyPointedSuperfusion S.data.object)).obj
  let Y := (H.forwardFunctor.data.obj (spanGenerator C.toWeaklyPointedSuperfusion T.data.object)).obj
  have hY : D.data.IsSimple Y := H.forwardFunctor.map_simple H.fullyFaithful H.map_grade_iff
    (spanGenerator C.toWeaklyPointedSuperfusion T.data.object) T.laws.simple
  let a := E.forwardFunctor.endSuperEquiv E.fullyFaithful (spanGenerator C.toWeaklyPointedSuperfusion S.data.object)
  let b := H.forwardFunctor.endSuperEquiv H.fullyFaithful (spanGenerator C.toWeaklyPointedSuperfusion T.data.object)
  let φ := tensorEndComparison C.toWeaklyPointedSuperfusion D.toWeaklyPointedSuperfusion
    S.data.object T.data.object X Y T.laws.simple hY a b
  have hφ : ∀ {p : ZMod 2} (f : @End (LinearCategory C.toWeaklyPointedSuperfusion) _
      (C.data.tensorObj S.data.object T.data.object)),
      D.data.IsHomogeneous p (φ.toAlgEquiv f) ↔ C.data.IsHomogeneous p f :=
    fun f => tensorEndComparison_grade_iff C.toWeaklyPointedSuperfusion D.toWeaklyPointedSuperfusion
      S.data.object T.data.object X Y T.laws.simple hY a b f
  obtain ⟨R, M, e, he, hm⟩ := exists_spanComparison_realizing_algebra C D
    (C.data.tensorObj S.data.object T.data.object) (D.data.tensorObj X Y)
    (tensorSimpleRetract C.toWeaklyPointedSuperfusion S T)
    (tensorSpanObject C.toWeaklyPointedSuperfusion S T).property φ.toAlgEquiv hφ
  refine ⟨R, M, e, he, ?_⟩
  intro f g
  exact (hm (C.data.tensorHom f g)).trans (congrArg (fun k => D.data.comp e.hom k)
    (tensorEndComparison_tensorHom C.toWeaklyPointedSuperfusion D.toWeaklyPointedSuperfusion
      S.data.object T.data.object X Y T.laws.simple hY a b f g))

end RMod.Classification
