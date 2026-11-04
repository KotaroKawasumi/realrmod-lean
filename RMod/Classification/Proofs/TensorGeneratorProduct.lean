import RMod.Classification.Proofs.TensorGeneratorComparison
import RMod.Classification.Proofs.SpanTargetOrbit
import RMod.Classification.Proofs.HomogeneousSpanTensor
import RMod.Classification.Instances.SpanChange
import RMod.Classification.Instances.SpanEquivalenceComposition

/-!
# Tensor comparison in the prescribed product component

The output of the ambient algebra realization lies in the intrinsic
product component: the image of the source simple retract is a retract
of the tensor product of the two generator images. Changing the target
span along this orbit identity leaves all ambient objects and maps
unchanged, so the tensor intertwining equation is retained exactly.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

theorem exists_tensorGeneratorComparison_in_product (C D : PiSuperfusion.{0, 0})
    (S T : SimpleObject C.toWeaklyPointedSuperfusion) (U V : SimpleObject D.toWeaklyPointedSuperfusion)
    (E : SpanSuperequivalence C.toWeaklyPointedSuperfusion D.toWeaklyPointedSuperfusion S.data.object U.data.object)
    (H : SpanSuperequivalence C.toWeaklyPointedSuperfusion D.toWeaklyPointedSuperfusion T.data.object V.data.object) :
    ∃ (M : SpanSuperequivalence C.toWeaklyPointedSuperfusion D.toWeaklyPointedSuperfusion
        (simpleTensorRepresentative C.toWeaklyPointedSuperfusion S T).data.object (simpleTensorRepresentative D.toWeaklyPointedSuperfusion U V).data.object)
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
  obtain ⟨R, M, e, he, hm⟩ := exists_tensorGeneratorComparison C D S T E H
  let W := simpleTensorRepresentative D.toWeaklyPointedSuperfusion U V
  let Q := simpleTensorRepresentative C.toWeaklyPointedSuperfusion S T
  let X := tensorSpanObject C.toWeaklyPointedSuperfusion S T
  let r := tensorSimpleRetract C.toWeaklyPointedSuperfusion S T
  have hXY := inHomogeneousSpan_tensor D.toWeaklyPointedSuperfusion U V
    (E.forwardFunctor.data.obj (spanGenerator C.toWeaklyPointedSuperfusion S.data.object)).property
    (H.forwardFunctor.data.obj (spanGenerator C.toWeaklyPointedSuperfusion T.data.object)).property
  have hMX := inHomogeneousSpan_of_retract D.toWeaklyPointedSuperfusion W.laws.simple hXY
    e.hom e.inv he.hom_inv he.hom_even
  let i : spanGenerator C.toWeaklyPointedSuperfusion Q.data.object ⟶ X :=
    ObjectProperty.homMk r.data.inclusion
  let p : X ⟶ spanGenerator C.toWeaklyPointedSuperfusion Q.data.object :=
    ObjectProperty.homMk r.data.projection
  have hip : i ≫ p = 𝟙 _ := by
    apply ObjectProperty.hom_ext
    exact r.laws.inclusion_projection
  have hRW := span_target_orbit_of_retract Q.laws.simple R.laws.simple W.laws.simple
    M X i p hip r.laws.inclusion_even hMX
  let N := spanChangeSuperequivalence D.toWeaklyPointedSuperfusion
    (inHomogeneousSpan_congr_generator D.toWeaklyPointedSuperfusion R.laws.simple W.laws.simple hRW)
  exact ⟨M.trans N, e, he, hm⟩

end RMod.Classification
