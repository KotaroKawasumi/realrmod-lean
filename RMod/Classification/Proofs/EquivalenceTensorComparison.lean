import RMod.Classification.Instances.EquivalenceTensorComparisonData
import RMod.Classification.Proofs.ConvolutionComponentReindex

/-!
# The image binary comparison has the target model's prescribed parity

The evaluated tensorator is even. The target projection-deletion pair
has degree nu' on the two image supports, and is invertible because the
image of a component object has its generator's support. Naturality
uses the original tensorator square and the actual convolution square.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (twistedPullback C hC t).toWeaklyPointedSuperfusion)

theorem equivalenceTensoratorComponent_evenIso (X Y : PullbackObj C s.data) (k : t.data.group) :
    EvenIsoLaws C.toWeaklyPointedSuperfusionData (equivalenceTensoratorComponentData C hC s t E X Y k) :=
  ⟨⟨congrFun (E.laws.forward.tensor_inv_hom X Y) k,
    congrFun (E.laws.forward.tensor_hom_inv X Y) k⟩,
    E.laws.forward.tensor_inv_even X Y k, E.laws.forward.tensor_hom_even X Y k⟩

variable (S T : SimpleObject (twistedPullback C hC s).toWeaklyPointedSuperfusion)

theorem equivalenceTensorComparison_homogeneousIso
    (X : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion S.data.object)
    (Y : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion T.data.object) :
    HomogeneousIsoLaws C.toWeaklyPointedSuperfusionData
      (t.data.nu (pullbackSimpleDegree C hC t (E.mapSimple S))
        (pullbackSimpleDegree C hC t (E.mapSimple T)))
      ((equivalenceTensorComparisonData C hC s t E S T).app X Y) := by
  have hX := pullback_span_supported C hC t (E.mapSimple S)
    ((E.spanRestriction S).forwardFunctor.data.obj X)
  have hn := convolutionComponentReindex_homogeneousIso C hC t.data
    (E.data.forward.obj X.obj) (E.data.forward.obj Y.obj) _ _ _
    (equivalenceTensorRightDegree_eq C hC s t E S T) hX
  have h := (equivalenceTensoratorComponent_evenIso C hC s t E X.obj Y.obj _).homogeneous.trans
    hC.toWeaklyPointedSuperfusionLaws hn
  rw [zero_add] at h
  exact h

theorem equivalenceTensorComparisonLaws :
    TensorComparisonLaws S T (pullbackReferenceSimple C hC s S) (pullbackReferenceSimple C hC s T)
      (t.data.nu (pullbackSimpleDegree C hC t (E.mapSimple S))
        (pullbackSimpleDegree C hC t (E.mapSimple T)))
      (equivalenceTensorComparisonData C hC s t E S T) where
  iso X Y := (equivalenceTensorComparison_homogeneousIso C hC s t E S T X Y).toIsoLaws
  hom_grade X Y := (equivalenceTensorComparison_homogeneousIso C hC s t E S T X Y).hom_grade
  inv_grade X Y := (equivalenceTensorComparison_homogeneousIso C hC s t E S T X Y).inv_grade
  naturality {X X' Y Y' a b} f q hf hq := by
    let k := pullbackSimpleDegree C hC t (E.mapSimple
      (simpleTensorRepresentative (twistedPullback C hC s).toWeaklyPointedSuperfusion S T))
    let i := equivalenceTensoratorComponentData C hC s t E X.obj Y.obj k
    let i' := equivalenceTensoratorComponentData C hC s t E X'.obj Y'.obj k
    let d := convolutionComponentReindexData C hC t.data (E.data.forward.obj X.obj) (E.data.forward.obj Y.obj)
      k _ _ (equivalenceTensorRightDegree_eq C hC s t E S T)
    let d' := convolutionComponentReindexData C hC t.data (E.data.forward.obj X'.obj) (E.data.forward.obj Y'.obj)
      k _ _ (equivalenceTensorRightDegree_eq C hC s t E S T)
    have hm := congrFun (E.laws.forward.tensor_inv_naturality
      (twistedPullback C hC t).laws.toWeaklyPointedSuperfusionLaws f.hom q.hom) k
    have hn := convolutionComponentReindex_naturality C hC t.data
      (E.data.forward.map f.hom) (E.data.forward.map q.hom)
      (E.laws.forward.map_grade f.hom hf) (E.laws.forward.map_grade q.hom hq)
      k _ _ (equivalenceTensorRightDegree_eq C hC s t E S T)
    let r := (-1 : ℝ) ^ ((t.data.nu (pullbackSimpleDegree C hC t (E.mapSimple S))
      (pullbackSimpleDegree C hC t (E.mapSimple T))) * (a + b)).val
    calc
      _ = C.comp (C.comp (E.data.forward.map
          ((twistedPullback C hC s).data.tensorHom f.hom q.hom) k) i'.hom) d'.hom :=
        (hC.comp_assoc _ _ _).symm
      _ = C.comp (C.comp i.hom (convolutionHom C hC t.data
          (E.data.forward.map f.hom) (E.data.forward.map q.hom) k)) d'.hom :=
        congrArg (fun m => C.comp m d'.hom) hm
      _ = C.comp i.hom (C.comp (convolutionHom C hC t.data
          (E.data.forward.map f.hom) (E.data.forward.map q.hom) k) d'.hom) := hC.comp_assoc _ _ _
      _ = C.comp i.hom (C.smul r (C.comp d.hom
          (C.tensorHom (E.data.forward.map f.hom (pullbackSimpleDegree C hC t (E.mapSimple S)))
            (E.data.forward.map q.hom (pullbackSimpleDegree C hC t (E.mapSimple T)))))) :=
        congrArg (C.comp i.hom) hn
      _ = _ := by rw [hC.comp_smul, ← hC.comp_assoc]; rfl

end RMod.Classification
