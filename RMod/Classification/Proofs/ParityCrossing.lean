import RMod.Classification.Proofs.ParityMultiplication

/-!
# The sign of exchanging two parity factors

Multiplying two factors after exchanging them differs from multiplication
in their original order by precisely the Koszul sign. The zero cases are
unitor cancellation; the odd-odd case is the proved self-crossing sign.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiLaws

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C) {p : PiData C} (hp : PiLaws C p)

include hC hp

theorem moveFactor_multiply (a b : ZMod 2) :
    C.comp (p.moveFactor a (p.factor b)).hom (p.multiplyFactors b a).hom =
      C.smul ((-1 : ℝ) ^ (a * b).val)
        (C.comp (p.multiplyFactors a b).hom
          (IsoData.ofEq C (congrArg p.factor (add_comm a b))).hom) := by
  rcases parity_cases a with rfl | rfl <;> rcases parity_cases b with rfl | rfl
  · change C.comp (C.comp (C.leftUnitorHom C.tensorUnit) (C.rightUnitorInv C.tensorUnit))
      (C.leftUnitorHom C.tensorUnit) =
      C.smul 1 (C.comp (C.leftUnitorHom C.tensorUnit) (C.id C.tensorUnit))
    rw [hC.one_smul, hC.comp_id, unitors_hom_equal hC, hC.comp_assoc,
      hC.right_unitor_inv_hom, hC.comp_id]
  · change C.comp (C.comp (C.leftUnitorHom p.object) (C.rightUnitorInv p.object))
      (C.rightUnitorHom p.object) = C.smul 1 (C.comp (C.leftUnitorHom p.object) (C.id p.object))
    rw [hC.one_smul, hC.comp_id, hC.comp_assoc, hC.right_unitor_inv_hom, hC.comp_id]
  · change C.comp (p.centralHom C.tensorUnit) (C.leftUnitorHom p.object) =
      C.smul 1 (C.comp (C.rightUnitorHom p.object) (C.id p.object))
    rw [hC.one_smul, hC.comp_id, hp.central_unit hC, hC.comp_assoc,
      hC.left_unitor_inv_hom, hC.comp_id]
  · change C.comp (p.centralHom p.object) p.contractionHom =
      C.smul ((-1 : ℝ) ^ 1) (C.comp p.contractionHom (C.id C.tensorUnit))
    rw [pow_one, hC.comp_id, hp.central_self hC, hC.smul_comp, hC.id_comp]

end RMod.Classification.PiLaws
