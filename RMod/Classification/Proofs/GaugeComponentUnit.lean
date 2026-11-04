import RMod.Classification.Proofs.GaugeComponentComparison
import RMod.Classification.Proofs.PullbackUnitLabel
import RMod.Classification.Proofs.Endomorphisms

/-!
# The parity change is normalized at the identity

At the group identity the source generator is the actual tensor unit.
The monoidal unit map supplies an even isomorphism to its image. Composing
it with the extracted comparison gives an invertible endomorphism of the
reference unit of degree lambda(1). End(1) is purely even and nonzero,
forcing that degree to be zero.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (twistedPullback C hC t).toWeaklyPointedSuperfusion)

theorem equivalenceGaugeLambda_one : equivalenceGaugeLambda C hC s t E 1 = 0 := by
  let S := pullbackDegreeSimple C hC s 1
  have hj := equivalenceReferenceComparison_at_source C hC s t E 1
    (spanGenerator (twistedPullback C hC s).toWeaklyPointedSuperfusion S.data.object)
  change C.HasHomogeneousIso (equivalenceGaugeLambda C hC s t E 1)
    (E.data.forward.obj S.data.object (pullbackSimpleDegree C hC t (E.mapSimple S))).val
    (S.data.object (pullbackSimpleDegree C hC s S)).val at hj
  dsimp only [S] at hj
  rw [equivalenceImageUnit_degree, pullbackSimpleDegree_placed,
    pullbackDegreeSimple_one_object] at hj
  change C.HasHomogeneousIso (equivalenceGaugeLambda C hC s t E 1)
    (E.data.forward.obj (twistedPullback C hC s).data.tensorUnit 1).val
    (pullbackUnitObj C hC s.data 1).val at hj
  rw [pullbackUnitObj, supportedObj_one] at hj
  have hi : C.HasHomogeneousIso 0 (pullbackUnitObj C hC t.data 1).val
      (E.data.forward.obj (twistedPullback C hC s).data.tensorUnit 1).val :=
    ⟨E.data.forward.unitHom 1, E.data.forward.unitInv 1,
      congrFun E.laws.forward.unit_hom_inv 1, congrFun E.laws.forward.unit_inv_hom 1,
      E.laws.forward.unit_hom_even 1, E.laws.forward.unit_inv_even 1⟩
  rw [pullbackUnitObj, supportedObj_one] at hi
  obtain ⟨f, f', hff', hf'f, hf, hf'⟩ := hi
  obtain ⟨j, j', hjj', hj'j, hj, hj'⟩ := hj
  have hfi : HomogeneousIsoLaws C.toWeaklyPointedSuperfusionData 0
      (⟨f, f'⟩ : IsoData C.toWeaklyPointedSuperfusionData _ _) := ⟨⟨hff', hf'f⟩, hf, hf'⟩
  have hji : HomogeneousIsoLaws C.toWeaklyPointedSuperfusionData
      (equivalenceGaugeLambda C hC s t E 1)
      (⟨j, j'⟩ : IsoData C.toWeaklyPointedSuperfusionData _ _) := ⟨⟨hjj', hj'j⟩, hj, hj'⟩
  have h := hfi.trans hC.toWeaklyPointedSuperfusionLaws hji
  rw [zero_add] at h
  rcases parity_cases (equivalenceGaugeLambda C hC s t E 1) with he | he
  · exact he
  · have hg := h.hom_grade
    rw [he] at hg
    have hz := (unit_end_odd_iff
      ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩ _).mp hg
    have hi := h.hom_inv
    rw [hz, raw_zero_comp hC.toWeaklyPointedSuperfusionLaws] at hi
    exact False.elim (simple_id_ne_zero hC.toWeaklyPointedSuperfusionLaws hC.simple_unit hi.symm)

end RMod.Classification
