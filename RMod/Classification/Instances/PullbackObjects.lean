import RMod.Classification.Abstract.Pullback
import RMod.Classification.Proofs.FiniteSums
import RMod.Classification.Proofs.UnitComponent

/-!
# Objects supported at the group identity

These are the initial object and morphism constructions for pullback. The
zero object is the chosen empty sum in C. The unit and parity objects retain
C's objects at the identity and are zero at every other group index. All
choices and maps come from C; no concrete regular-module data is imported.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

/-- The zero family, using the same empty-sum object in every component. -/
noncomputable def pullbackZeroObj : PullbackObj C t := fun g =>
  ⟨((finiteSumsData C hC.toWeaklyPointedSuperfusionLaws).sum
    (Fin.elim0 : Fin 0 → C.Obj)).object,
    finiteSums_inComponent C hC Fin.elim0 (Multiplicative.toAdd (t.rho g))
      (fun i => Fin.elim0 i)⟩

/-- Extend an object in the neutral component by zero at all other indices. -/
noncomputable def supportedObj (X : C.Obj)
    (hX : InComponent C.toWeaklyPointedSuperfusionData 0 X) : PullbackObj C t := by
  classical
  exact fun g => ⟨if g = 1 then X else (pullbackZeroObj C hC t g).val, by
    split_ifs with hg
    · simpa only [hg, map_one, toAdd_one] using hX
    · exact (pullbackZeroObj C hC t g).property⟩

/-- Extend a morphism by zero, between the specified supported objects. -/
noncomputable def supportedHom {X Y : C.Obj}
    (hX : InComponent C.toWeaklyPointedSuperfusionData 0 X)
    (hY : InComponent C.toWeaklyPointedSuperfusionData 0 Y) (f : C.Hom X Y) :
    PullbackHom C t (supportedObj C hC t X hX) (supportedObj C hC t Y hY) := by
  classical
  intro g
  by_cases hg : g = 1
  · simpa only [supportedObj, if_pos hg] using f
  · exact C.zero

noncomputable def pullbackUnitObj : PullbackObj C t :=
  supportedObj C hC t C.tensorUnit (InComponent.tensor_unit hC)

noncomputable def pullbackPiObj : PullbackObj C t :=
  supportedObj C hC t C.pi.object (InComponent.parity_object hC)

noncomputable def pullbackPiHom :
    PullbackHom C t (pullbackPiObj C hC t) (pullbackUnitObj C hC t) :=
  supportedHom C hC t (InComponent.parity_object hC) (InComponent.tensor_unit hC) C.pi.hom

noncomputable def pullbackPiInv :
    PullbackHom C t (pullbackUnitObj C hC t) (pullbackPiObj C hC t) :=
  supportedHom C hC t (InComponent.tensor_unit hC) (InComponent.parity_object hC) C.pi.inv

end RMod.Classification
