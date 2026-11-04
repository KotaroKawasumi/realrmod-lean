import RMod.Classification.Instances.Duals
import RMod.Classification.Proofs.UnitSplitting
import RMod.Classification.Proofs.ZeroObjects

/-!
# Nonvanishing of tensor products

The snake identity makes the coevaluation of a nonzero object nonzero.
Semisimplicity and the split unit give it a retraction. Tensor this retract
with a second object: if their tensor product were zero, associativity
would make the second object a retract of zero. No pivotal structure or
tensor-endomorphism isomorphism is used in this argument.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {C : WeaklyPointedSuperfusion.{0, 0}}

namespace DualPairing

variable {X Y : C.data.Obj} (p : DualPairing C X Y)

theorem coeval_ne_zero (hX : C.data.id X ≠ C.data.zero) : p.data.coeval ≠ C.data.zero := by
  intro he
  have h := p.laws.snake_left
  dsimp only [WeaklyPointedSuperfusionData.whiskerRight] at h
  rw [he, tensor_zero_left C.laws, raw_zero_comp C.laws, raw_zero_comp C.laws] at h
  apply hX
  have heq := congrArg (fun f => C.data.comp (C.data.comp (C.data.leftUnitorInv X) f)
    (C.data.rightUnitorHom X)) h.symm
  simp only [C.laws.comp_assoc, C.laws.right_unitor_inv_hom, C.laws.comp_id,
    C.laws.left_unitor_inv_hom, raw_comp_zero C.laws, raw_zero_comp C.laws] at heq
  exact heq

theorem eval_ne_zero (hX : C.data.id X ≠ C.data.zero) : p.data.eval ≠ C.data.zero := by
  intro he
  have h := p.laws.snake_left
  dsimp only [WeaklyPointedSuperfusionData.whiskerLeft] at h
  rw [he, tensor_zero_right C.laws, raw_comp_zero C.laws] at h
  apply hX
  have heq := congrArg (fun f => C.data.comp (C.data.comp (C.data.leftUnitorInv X) f)
    (C.data.rightUnitorHom X)) h.symm
  simp only [C.laws.comp_assoc, C.laws.right_unitor_inv_hom, C.laws.comp_id,
    C.laws.left_unitor_inv_hom, raw_comp_zero C.laws, raw_zero_comp C.laws] at heq
  exact heq

end DualPairing

theorem tensor_id_ne_zero {U V : C.data.Obj} (hU : C.data.id U ≠ C.data.zero)
    (hV : C.data.id V ≠ C.data.zero) : C.data.id (C.data.tensorObj U V) ≠ C.data.zero := by
  intro hUV
  let p := (dualChoices C).rightPairing V
  obtain ⟨cap, hcap⟩ := unit_retraction C p.data.coeval (p.coeval_ne_zero hV)
  have hz : C.data.id (C.data.tensorObj (C.data.tensorObj U V) ((dualChoices C).data.rightObj V)) =
      C.data.zero := tensor_id_zero_left C.laws hUV _
  have hz' := id_zero_of_retract C.laws (C.data.associatorInv U V _)
    (C.data.associatorHom U V _) (C.laws.associator_inv_hom U V _) hz
  have hr : C.data.comp (C.data.tensorHom (C.data.id U) p.data.coeval)
      (C.data.tensorHom (C.data.id U) cap) = C.data.id (C.data.tensorObj U C.data.tensorUnit) := by
    rw [interchange_first_even C.laws _ _ _ _ (C.laws.id_even U),
      C.laws.comp_id, hcap, C.laws.tensor_id]
  have hu := id_zero_of_retract C.laws _ _ hr hz'
  exact hU (id_zero_of_retract C.laws (C.data.rightUnitorInv U) (C.data.rightUnitorHom U)
    (C.laws.right_unitor_inv_hom U) hu)

end RMod.Classification
