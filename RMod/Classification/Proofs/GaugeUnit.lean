import RMod.Classification.Instances.GaugeUnit
import RMod.Classification.Proofs.IsoCalculus

/-! # The specified gauge unit comparison is an even isomorphism -/

set_option autoImplicit false

namespace RMod.Classification

theorem gaugeUnitComponent_evenIso
    (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
    (d : GaugeData s.data t.data) (hρ : ∀ g, t.data.rho (d.phi g) = s.data.rho g)
    (hlam : d.lam 1 = 0) (k : t.data.group) :
    EvenIsoLaws C.toWeaklyPointedSuperfusionData (gaugeUnitComponentData C hC s t d hρ hlam k) := by
  classical
  by_cases hk : k = 1
  · subst k
    simp only [gaugeUnitComponentData]
    exact (EvenIsoLaws.ofEq hC.toWeaklyPointedSuperfusionLaws _).trans
      hC.toWeaklyPointedSuperfusionLaws
      ((EvenIsoLaws.rightUnit hC.toWeaklyPointedSuperfusionLaws C.tensorUnit).symm.trans
        hC.toWeaklyPointedSuperfusionLaws (EvenIsoLaws.ofEq hC.toWeaklyPointedSuperfusionLaws _))
  · simp only [gaugeUnitComponentData, dif_neg hk]
    exact
      { hom_inv := (raw_zero_comp hC.toWeaklyPointedSuperfusionLaws _).trans
          (gaugeTargetUnit_zero C hC t k hk).symm
        inv_hom := (raw_zero_comp hC.toWeaklyPointedSuperfusionLaws _).trans
          (gaugeImageUnit_zero C hC s t d hρ k hk).symm
        hom_even := hC.grade_zero _ _ _
        inv_even := hC.grade_zero _ _ _ }

end RMod.Classification
