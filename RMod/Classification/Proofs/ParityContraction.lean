import RMod.Classification.Proofs.ParityHalfBraiding

/-!
# Associativity of the parity contraction

The signed contraction is the composite of the left odd deletion with
the specified odd map. The unit triangle identifies deletion in a middle
position with right deletion. On three parity factors the two minus signs
from exchanging left and right deletion cancel, giving the associativity
identity with all associators and unitors displayed.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiLaws

attribute [local implicit_reducible] PiData.shiftObj

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C) {p : PiData C} (hp : PiLaws C p)

include hC hp

theorem contraction_eq_z : p.contractionHom = C.comp (p.zHom p.object) p.hom := by
  unfold PiData.contractionHom PiData.zHom
  rw [hC.comp_assoc, ← hC.left_unitor_naturality p.hom, ← hC.comp_assoc,
    hC.super_interchange _ _ _ _ hp.hom_odd hp.hom_odd]
  simp only [one_mul, ZMod.val_one, pow_one, hC.comp_id, hC.id_comp, hC.smul_comp,
    Calculus.neg_as_smul hC]

theorem z_self_eq_neg_rightZ : p.zHom p.object = C.smul (-1) (p.rightZHom p.object) := by
  rw [← hp.central_rightZ hC p.object, hp.central_self hC, hC.smul_comp, hC.id_comp]

theorem contraction_assoc :
    C.comp (C.tensorHom p.contractionHom (C.id p.object)) (C.leftUnitorHom p.object) =
      C.comp (C.comp (C.associatorHom p.object p.object p.object)
        (C.tensorHom (C.id p.object) p.contractionHom)) (C.rightUnitorHom p.object) := by
  have hl : C.comp (C.tensorHom p.contractionHom (C.id p.object)) (C.leftUnitorHom p.object) =
      C.comp (C.tensorHom (p.zHom p.object) (C.id p.object)) (p.zHom p.object) := by
    rw [hp.contraction_eq_z hC]
    have ht := (tensorRightLaws ⟨C, hC⟩ p.object).map_comp (p.zHom p.object) p.hom
    change C.tensorHom (C.comp (p.zHom p.object) p.hom) (C.id p.object) =
      C.comp (C.tensorHom (p.zHom p.object) (C.id p.object))
        (C.tensorHom p.hom (C.id p.object)) at ht
    rw [ht, hC.comp_assoc]
    rfl
  have hr : C.comp (C.comp (C.associatorHom p.object p.object p.object)
        (C.tensorHom (C.id p.object) p.contractionHom)) (C.rightUnitorHom p.object) =
      C.comp (C.tensorHom (p.rightZHom p.object) (C.id p.object)) (p.rightZHom p.object) := by
    rw [hp.contraction_eq_z hC]
    have ht := (tensorLeftLaws ⟨C, hC⟩ p.object).map_comp (p.zHom p.object) p.hom
    change C.tensorHom (C.id p.object) (C.comp (p.zHom p.object) p.hom) =
      C.comp (C.tensorHom (C.id p.object) (p.zHom p.object))
        (C.tensorHom (C.id p.object) p.hom) at ht
    rw [ht, ← hC.comp_assoc, rightZ_middle hC, hC.comp_assoc]
    rfl
  rw [hl, hr, hp.z_self_eq_neg_rightZ hC, hC.tensor_smul_left, hC.smul_comp,
    hC.comp_smul, ← hC.mul_smul]
  simp only [neg_mul_neg, one_mul, hC.one_smul]

end RMod.Classification.PiLaws
