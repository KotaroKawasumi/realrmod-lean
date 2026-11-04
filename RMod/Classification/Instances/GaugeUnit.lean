import RMod.Classification.Proofs.GaugeUnitObjects
import RMod.Classification.Abstract.Normalizers

/-!
# The specified unit comparison for the gauge functor

At the group identity use the inverse right unitor, retaining the two
object equality maps. All other coordinates are the unique maps between
zero objects. The construction uses lambda(1)=0 and no scalar choices.
-/

set_option autoImplicit false

namespace RMod.Classification

noncomputable def gaugeUnitComponentData
    (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
    (d : GaugeData s.data t.data) (hρ : ∀ g, t.data.rho (d.phi g) = s.data.rho g)
    (hlam : d.lam 1 = 0) (k : t.data.group) :
    IsoData C.toWeaklyPointedSuperfusionData (pullbackUnitObj C hC t.data k).val
      (((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj
        (pullbackUnitObj C hC s.data)) k).val := by
  classical
  by_cases hk : k = 1
  · subst k
    exact (IsoData.ofEq C.toWeaklyPointedSuperfusionData
      (supportedObj_one C hC t.data C.tensorUnit (InComponent.tensor_unit hC))).trans
      C.toWeaklyPointedSuperfusionData
      (((IsoData.rightUnit C.toWeaklyPointedSuperfusionData C.tensorUnit).symm
        C.toWeaklyPointedSuperfusionData).trans C.toWeaklyPointedSuperfusionData
        (IsoData.ofEq C.toWeaklyPointedSuperfusionData (gaugeImageUnit_one C hC s t d hρ hlam).symm))
  · exact ⟨C.zero, C.zero⟩

end RMod.Classification
