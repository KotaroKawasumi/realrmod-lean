import RMod.Classification.Instances.GaugeComponentParity
import RMod.Classification.Proofs.HomogeneousIsoCalculus

/-!
# Returning component comparisons to the original model objects

The unit of source evaluation identifies an actual model object with its
chosen inverse image. Map this even isomorphism through the equivalence
and target evaluation, then compose with the selected homogeneous natural
comparison. This retains its degree on the original object's coordinates.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (twistedPullback C hC t).toWeaklyPointedSuperfusion)

theorem equivalenceReferenceComparison_at_source (g : s.data.group)
    (X : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s g).data.object) :
    C.HasHomogeneousIso (equivalenceGaugeLambda C hC s t E g)
      (E.data.forward.obj X.obj
        (pullbackSimpleDegree C hC t (E.mapSimple (pullbackDegreeSimple C hC s g)))).val
      (X.obj (pullbackSimpleDegree C hC s (pullbackDegreeSimple C hC s g))).val := by
  let S := pullbackDegreeSimple C hC s g
  let V := pullbackSpanEvaluationEquivalence C hC s S
  let K := (E.spanRestriction S).forwardFunctor.comp
    (pullbackSpanEvaluationEquivalence C hC t (E.mapSimple S)).forwardFunctor
  let i := K.toFunctor.mapIso (V.data.unitIso.app X)
  let j := (equivalenceReferenceComparison C hC s t E g).appIso (V.data.functor.obj X)
  let di : IsoData C.toWeaklyPointedSuperfusionData _ _ := ⟨i.hom.hom, i.inv.hom⟩
  let dj : IsoData C.toWeaklyPointedSuperfusionData _ _ := ⟨j.hom.hom, j.inv.hom⟩
  have hi : HomogeneousIsoLaws C.toWeaklyPointedSuperfusionData 0 di :=
    ⟨⟨congrArg (fun f => f.hom) i.hom_inv_id, congrArg (fun f => f.hom) i.inv_hom_id⟩,
      K.laws.map_grade _ (V.laws.unit_hom_even X),
      K.laws.map_grade _ (V.laws.unit_inv_even X)⟩
  have hj : HomogeneousIsoLaws C.toWeaklyPointedSuperfusionData
      (equivalenceGaugeLambda C hC s t E g) dj :=
    ⟨⟨congrArg (fun f => f.hom) j.hom_inv_id, congrArg (fun f => f.hom) j.inv_hom_id⟩,
      (equivalenceReferenceComparison C hC s t E g).laws.grade (V.data.functor.obj X),
      (equivalenceReferenceComparison C hC s t E g).laws.inverse.grade (V.data.functor.obj X)⟩
  have hij := hi.trans hC.toWeaklyPointedSuperfusionLaws hj
  rw [zero_add] at hij
  exact ⟨_, _, hij.hom_inv, hij.inv_hom, hij.hom_grade, hij.inv_grade⟩

end RMod.Classification
