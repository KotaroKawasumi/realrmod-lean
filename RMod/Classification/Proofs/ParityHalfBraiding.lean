import RMod.Classification.Proofs.CentralNaturality
import RMod.Classification.Proofs.StructuralCoherence
import RMod.Classification.Instances.TensorFunctors

/-!
# Coherence of the parity central comparison

Deleting the parity factor on the left is compatible with tensoring.
The unit triangle gives the analogous deletion in a middle position.
These identities are derived using the actual odd map and even structural
coherence, keeping each interchange sign explicit.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiLaws

attribute [local implicit_reducible] PiData.shiftObj

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C) {p : PiData C} (hp : PiLaws C p)

include hC

theorem z_tensor (X Y : C.Obj) :
    C.comp (C.associatorHom p.object X Y) (p.zHom (C.tensorObj X Y)) =
      C.tensorHom (p.zHom X) (C.id Y) := by
  unfold PiData.zHom
  rw [← hC.tensor_id X Y, ← hC.comp_assoc, ← hC.associator_naturality,
    hC.comp_assoc, leftUnitor_tensor hC]
  exact ((tensorRightLaws ⟨C, hC⟩ Y).map_comp _ _).symm

theorem rightZ_middle (X Y : C.Obj) :
    C.comp (C.associatorHom X p.object Y) (C.tensorHom (C.id X) (p.zHom Y)) =
      C.tensorHom (p.rightZHom X) (C.id Y) := by
  unfold PiData.zHom PiData.rightZHom
  have ht := (tensorLeftLaws ⟨C, hC⟩ X).map_comp
    (C.tensorHom p.hom (C.id Y)) (C.leftUnitorHom Y)
  change C.tensorHom (C.id X) (C.comp (C.tensorHom p.hom (C.id Y)) (C.leftUnitorHom Y)) =
    C.comp (C.tensorHom (C.id X) (C.tensorHom p.hom (C.id Y)))
      (C.tensorHom (C.id X) (C.leftUnitorHom Y)) at ht
  rw [ht, ← hC.comp_assoc, ← hC.associator_naturality, hC.comp_assoc]
  change C.comp (C.tensorHom (C.tensorHom (C.id X) p.hom) (C.id Y))
      (C.comp (C.associatorHom X C.tensorUnit Y) (C.whiskerLeft X (C.leftUnitorHom Y))) = _
  rw [hC.triangle]
  change C.comp (C.tensorHom (C.tensorHom (C.id X) p.hom) (C.id Y))
      (C.tensorHom (C.rightUnitorHom X) (C.id Y)) = _
  exact ((tensorRightLaws ⟨C, hC⟩ Y).map_comp _ _).symm

theorem rightZ_tensor (X Y : C.Obj) :
    p.rightZHom (C.tensorObj X Y) =
      C.comp (C.associatorHom X Y p.object) (C.tensorHom (C.id X) (p.rightZHom Y)) := by
  unfold PiData.rightZHom
  rw [rightUnitor_tensor hC, ← hC.comp_assoc, ← hC.tensor_id X Y,
    hC.associator_naturality, hC.comp_assoc]
  congr 1
  exact ((tensorLeftLaws ⟨C, hC⟩ X).map_comp _ _).symm

include hp

/-- The half-braiding equation, with both endpoint associators displayed. -/
theorem central_tensor (X Y : C.Obj) :
    C.comp (C.comp (C.associatorHom p.object X Y) (p.centralHom (C.tensorObj X Y)))
        (C.associatorHom X Y p.object) =
      C.comp (C.comp (C.tensorHom (p.centralHom X) (C.id Y)) (C.associatorHom X p.object Y))
        (C.tensorHom (C.id X) (p.centralHom Y)) := by
  have hc := (tensorLeftLaws ⟨C, hC⟩ X).map_comp (p.centralHom Y) (p.rightZHom Y)
  change C.tensorHom (C.id X) (C.comp (p.centralHom Y) (p.rightZHom Y)) =
    C.comp (C.tensorHom (C.id X) (p.centralHom Y)) (C.tensorHom (C.id X) (p.rightZHom Y)) at hc
  have ht :
      C.comp (C.comp (C.comp (C.associatorHom p.object X Y) (p.centralHom (C.tensorObj X Y)))
          (C.associatorHom X Y p.object)) (C.tensorHom (C.id X) (p.rightZHom Y)) =
        C.comp (C.comp (C.comp (C.tensorHom (p.centralHom X) (C.id Y))
          (C.associatorHom X p.object Y)) (C.tensorHom (C.id X) (p.centralHom Y)))
          (C.tensorHom (C.id X) (p.rightZHom Y)) := by
    calc
      _ = C.tensorHom (p.zHom X) (C.id Y) := by
        rw [hC.comp_assoc, ← rightZ_tensor hC, hC.comp_assoc,
          hp.central_rightZ hC, z_tensor hC]
      _ = C.comp (C.tensorHom (p.centralHom X) (C.id Y))
          (C.tensorHom (p.rightZHom X) (C.id Y)) := by
        rw [← hp.central_rightZ hC X]
        exact (tensorRightLaws ⟨C, hC⟩ Y).map_comp _ _
      _ = _ := by
        rw [hC.comp_assoc, ← hc, hp.central_rightZ hC Y, hC.comp_assoc, rightZ_middle hC]
  have hi : C.comp (C.tensorHom (C.id X) (p.rightZHom Y))
      (C.tensorHom (C.id X) (p.rightZInv Y)) = C.id (C.tensorObj X (C.tensorObj Y p.object)) := by
    rw [interchange_first_even hC _ _ _ _ (hC.id_even X), hC.id_comp,
      (hp.rightZ_iso hC Y).hom_inv, hC.tensor_id]
  have ht' := congrArg (fun f => C.comp f (C.tensorHom (C.id X) (p.rightZInv Y))) ht
  simpa only [hC.comp_assoc, hi, hC.comp_id] using ht'

/-- Exchanging the two specified parity factors introduces exactly -1. -/
theorem central_self :
    p.centralHom p.object = C.smul (-1) (C.id (C.tensorObj p.object p.object)) := by
  have hz : C.comp (p.zHom p.object) p.hom =
      C.smul (-1) (C.comp (p.rightZHom p.object) p.hom) := by
    rw [rightZ_comp hC, PiData.zHom, hC.comp_assoc,
      ← hC.left_unitor_naturality p.hom, ← hC.comp_assoc,
      hC.super_interchange _ _ _ _ hp.hom_odd hp.hom_odd]
    simp only [one_mul, ZMod.val_one, pow_one, hC.comp_id, hC.id_comp,
      hC.smul_comp, unitors_hom_equal hC]
  have hz' := congrArg (fun f => C.comp f p.inv) hz
  have he : p.zHom p.object = C.smul (-1) (p.rightZHom p.object) := by
    simpa only [hC.smul_comp, hC.comp_assoc, hp.hom_inv, hC.comp_id] using hz'
  have he' := congrArg (fun f => C.comp f (p.rightZInv p.object)) he
  rw [← hp.central_rightZ hC p.object, hC.comp_assoc, hC.smul_comp,
    (hp.rightZ_iso hC p.object).hom_inv, hC.comp_id] at he'
  exact he'

end RMod.Classification.PiLaws
