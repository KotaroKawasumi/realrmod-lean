import RMod.Classification.Instances.GaugeUnderlyingFunctor
import RMod.Classification.Proofs.PullbackObjects
import RMod.Classification.Proofs.ZeroObjects

/-!
# The unit and its gauge image at every group coordinate

At the identity, normalization of lambda gives the actual object
one tensor one. Away from the identity, both unit families have zero
identity; right tensoring preserves this zero-object property.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (d : GaugeData s.data t.data) (hρ : ∀ g, t.data.rho (d.phi g) = s.data.rho g)

theorem gaugeImageUnit_one (hlam : d.lam 1 = 0) :
    (((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj
      (pullbackUnitObj C hC s.data)) 1).val = C.tensorObj C.tensorUnit C.tensorUnit := by
  change C.tensorObj (pullbackUnitObj C hC s.data (d.phi.symm 1)).val
    (C.pi.factor (d.lam (d.phi.symm 1))) = _
  rw [map_one d.phi.symm, hlam, pullbackUnitObj, supportedObj_one]
  rfl

omit s d hρ in
theorem gaugeTargetUnit_zero (k : t.data.group) (hk : k ≠ 1) :
    C.id (pullbackUnitObj C hC t.data k).val = C.zero := by
  rw [pullbackUnitObj, supportedObj_ne_one C hC t.data _ _ k hk]
  exact pullbackZero_id C hC t.data k

theorem gaugeImageUnit_zero (k : t.data.group) (hk : k ≠ 1) :
    C.id (((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj
      (pullbackUnitObj C hC s.data)) k).val = C.zero := by
  have hi : d.phi.symm k ≠ 1 := fun he => hk (d.phi.symm.injective (he.trans (map_one d.phi.symm).symm))
  exact tensor_id_zero_left hC.toWeaklyPointedSuperfusionLaws
    (gaugeTargetUnit_zero C hC s (d.phi.symm k) hi) _

end RMod.Classification
