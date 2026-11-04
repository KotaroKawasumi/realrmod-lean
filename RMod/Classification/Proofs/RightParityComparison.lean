import RMod.Classification.Instances.RightParityComparison
import RMod.Classification.Proofs.Pi
import RMod.Classification.Proofs.TensorCalculus

/-!
# The right odd comparison and its naturality sign

The tensor identity on the ordinary object removes the sign from the
inverse equations. Naturality has one crossing of the odd comparison
with the input map, so its scalar is exactly the input parity sign.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiLaws

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C) {p : PiData C} (hp : PiLaws C p)

include hC hp

theorem rightZ_iso (X : C.Obj) :
    IsoLaws C (⟨p.rightZHom X, p.rightZInv X⟩ : IsoData C _ _) := by
  have hi : IsoLaws C
      (⟨C.tensorHom (C.id X) p.hom, C.tensorHom (C.id X) p.inv⟩ : IsoData C _ _) := by
    constructor
    · change C.comp (C.tensorHom (C.id X) p.hom) (C.tensorHom (C.id X) p.inv) = _
      rw [interchange_first_even hC _ _ _ _ (hC.id_even X),
        hC.id_comp, hp.hom_inv, hC.tensor_id]
    · change C.comp (C.tensorHom (C.id X) p.inv) (C.tensorHom (C.id X) p.hom) = _
      rw [interchange_first_even hC _ _ _ _ (hC.id_even X),
        hC.id_comp, hp.inv_hom, hC.tensor_id]
  exact hi.trans hC (IsoLaws.rightUnit hC X)

theorem rightZ_hom_odd (X : C.Obj) : C.IsHomogeneous 1 (p.rightZHom X) := by
  have h := hC.comp_grade _ _ (hC.tensor_grade _ _ (hC.id_even X) hp.hom_odd)
    (hC.right_unitor_hom_even X)
  change C.IsHomogeneous ((0 + 1) + 0) (p.rightZHom X) at h
  simpa only [zero_add, add_zero] using h

theorem rightZ_inv_odd (X : C.Obj) : C.IsHomogeneous 1 (p.rightZInv X) := by
  have h := hC.comp_grade _ _ (hC.right_unitor_inv_even X)
    (hC.tensor_grade _ _ (hC.id_even X) hp.inv_odd)
  change C.IsHomogeneous (0 + (0 + 1)) (p.rightZInv X) at h
  simpa only [zero_add] using h

omit hp in
theorem rightZ_comp {X Y : C.Obj} (f : C.Hom X Y) :
    C.comp (p.rightZHom X) f = C.comp (C.tensorHom f p.hom) (C.rightUnitorHom Y) := by
  unfold PiData.rightZHom
  rw [hC.comp_assoc, ← hC.right_unitor_naturality f, ← hC.comp_assoc,
    interchange_second_even hC _ _ _ _ (hC.id_even _), hC.id_comp, hC.comp_id]

theorem rightZ_naturality {X Y : C.Obj} {a : ZMod 2} (f : C.Hom X Y)
    (hf : C.IsHomogeneous a f) :
    C.comp (C.tensorHom f (C.id p.object)) (p.rightZHom Y) =
      C.smul ((-1 : ℝ) ^ a.val) (C.comp (p.rightZHom X) f) := by
  rw [rightZ_comp hC]
  unfold PiData.rightZHom
  rw [← hC.comp_assoc, hC.super_interchange _ _ _ _ hp.hom_odd hf]
  simp only [one_mul, hC.comp_id, hC.id_comp, hC.smul_comp]

end RMod.Classification.PiLaws
