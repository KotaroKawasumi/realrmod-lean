import RMod.BrundanEllis.StackingReferenceUniformExchange
import RMod.BrundanEllis.StackingReferenceValue

/-! Actual exchanges in the reference category used by public pullbacks.
Their labels are intrinsic component hypotheses, and every homogeneous
naturality equation is inherited from the concrete coefficient calculation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace RMod.BrundanEllis.Stacking
open Superfusion Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT RMod.Classification

/-- The reference exchange between two specified intrinsic components. -/
def referenceExchange (a b : ZMod 8) (X Y : reference.data.Obj)
    (hX : InComponent reference.data.toWeaklyPointedSuperfusionData a X)
    (hY : InComponent reference.data.toWeaklyPointedSuperfusionData b Y) :
    reference.data.Hom (reference.data.tensorObj X Y) (reference.data.tensorObj Y X) :=
  referenceLift (ReferenceCommutor.uniformExchange a b X Y
    (reference_component_label hX) (reference_component_label hY))

def referenceExchangeInv (a b : ZMod 8) (X Y : reference.data.Obj)
    (hX : InComponent reference.data.toWeaklyPointedSuperfusionData a X)
    (hY : InComponent reference.data.toWeaklyPointedSuperfusionData b Y) :
    reference.data.Hom (reference.data.tensorObj Y X) (reference.data.tensorObj X Y) :=
  referenceLift (ReferenceCommutor.uniformExchangeInv a b X Y
    (reference_component_label hX) (reference_component_label hY))

theorem referenceExchange_grade (a b : ZMod 8) (X Y : reference.data.Obj)
    (hX : InComponent reference.data.toWeaklyPointedSuperfusionData a X)
    (hY : InComponent reference.data.toWeaklyPointedSuperfusionData b Y) :
    reference.data.IsHomogeneous (ReferenceCommutor.degree a b) (referenceExchange a b X Y hX hY) := by
  apply (referenceValue_grade _ _).mpr
  rw [referenceExchange, referenceValue_lift]
  exact ReferenceCommutor.uniformExchange_grade a b X Y _ _

theorem referenceExchangeInv_grade (a b : ZMod 8) (X Y : reference.data.Obj)
    (hX : InComponent reference.data.toWeaklyPointedSuperfusionData a X)
    (hY : InComponent reference.data.toWeaklyPointedSuperfusionData b Y) :
    reference.data.IsHomogeneous (ReferenceCommutor.degree a b) (referenceExchangeInv a b X Y hX hY) := by
  apply (referenceValue_grade _ _).mpr
  rw [referenceExchangeInv, referenceValue_lift]
  exact ReferenceCommutor.uniformExchangeInv_grade a b X Y _ _

theorem referenceValue_injective {X Y : reference.data.Obj} :
    Function.Injective (@referenceValue X Y) := by
  intro f g h
  exact (referenceLift_value f).symm.trans ((congrArg referenceLift h).trans (referenceLift_value g))

theorem referenceExchange_inverse (a b : ZMod 8) (X Y : reference.data.Obj)
    (hX : InComponent reference.data.toWeaklyPointedSuperfusionData a X)
    (hY : InComponent reference.data.toWeaklyPointedSuperfusionData b Y) :
    reference.data.comp (referenceExchange a b X Y hX hY) (referenceExchangeInv a b X Y hX hY) =
      reference.data.id (reference.data.tensorObj X Y) ∧
    reference.data.comp (referenceExchangeInv a b X Y hX hY) (referenceExchange a b X Y hX hY) =
      reference.data.id (reference.data.tensorObj Y X) := by
  have h := ReferenceCommutor.uniformExchange_inverse a b X Y
    (reference_component_label hX) (reference_component_label hY)
  constructor
  · apply referenceValue_injective
    simp only [referenceValue_comp, referenceValue_id, referenceExchange, referenceExchangeInv,
      referenceValue_lift]
    with_unfolding_all exact h.1
  · apply referenceValue_injective
    simp only [referenceValue_comp, referenceValue_id, referenceExchange, referenceExchangeInv,
      referenceValue_lift]
    with_unfolding_all exact h.2

/-- Signed naturality for every pair of homogeneous reference morphisms. -/
theorem referenceExchange_naturality (a b : ZMod 8) (X X' Y Y' : reference.data.Obj)
    (hX : InComponent reference.data.toWeaklyPointedSuperfusionData a X)
    (hX' : InComponent reference.data.toWeaklyPointedSuperfusionData a X')
    (hY : InComponent reference.data.toWeaklyPointedSuperfusionData b Y)
    (hY' : InComponent reference.data.toWeaklyPointedSuperfusionData b Y')
    (f : reference.data.Hom X X') (g : reference.data.Hom Y Y') (d e : ZMod 2)
    (hf : reference.data.IsHomogeneous d f) (hg : reference.data.IsHomogeneous e g) :
    reference.data.comp (reference.data.tensorHom f g) (referenceExchange a b X' Y' hX' hY') =
    reference.data.smul (paritySign (ReferenceCommutor.degree a b * (d + e) + d * e))
      (reference.data.comp (referenceExchange a b X Y hX hY) (reference.data.tensorHom g f)) := by
  apply referenceValue_injective
  simpa only [referenceValue_comp, referenceValue_tensor, referenceValue_smul, referenceExchange,
    referenceValue_lift] using
    ReferenceCommutor.uniformExchange_naturality a b X X' Y Y'
      (reference_component_label hX) (reference_component_label hX')
      (reference_component_label hY) (reference_component_label hY')
      (referenceValue f) (referenceValue g) d e
      ((referenceValue_grade d f).mp hf) ((referenceValue_grade e g).mp hg)

/-- A concrete shifted singleton has its specified reference component. -/
theorem referenceSingleton_component (a : ZMod 8) (p : ZMod 2) :
    InComponent reference.data.toWeaklyPointedSuperfusionData a (Obj.singleton (a, p)) :=
  InComponent.of_simple referenceProperty
    ((reference_simple_iff _).mpr (realSingleton_simple a p))
    ((reference_type_iff _ _).mpr ((realSingleton_type_iff a p a).mpr rfl))

/-- Two odd Clifford labels give an odd exchange in the public reference. -/
example : reference.data.IsHomogeneous 1
    (referenceExchange 1 3 (Obj.singleton (1, 0)) (Obj.singleton (3, 1))
      (referenceSingleton_component 1 0) (referenceSingleton_component 3 1)) :=
  referenceExchange_grade 1 3 _ _ _ _

/-- The exchange of types 2 and 4 is even despite the nonzero input shift. -/
example : reference.data.IsHomogeneous 0
    (referenceExchange 2 4 (Obj.singleton (2, 1)) (Obj.singleton (4, 0))
      (referenceSingleton_component 2 1) (referenceSingleton_component 4 0)) :=
  referenceExchange_grade 2 4 _ _ _ _

end RMod.BrundanEllis.Stacking
