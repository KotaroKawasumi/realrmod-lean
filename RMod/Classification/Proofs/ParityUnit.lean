import RMod.Classification.Proofs.ParityContractionCentral

/-!
# The parity comparison at the tensor unit

Left and right odd deletion at the unit reduce to the specified odd map
after the respective unitors. Consequently the central comparison at the
unit is exactly the canonical unitor composite. No scalar normalization
is left undetermined by these equations.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiLaws

attribute [local implicit_reducible] PiData.shiftObj

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C) {p : PiData C} (hp : PiLaws C p)

include hC

theorem z_unit : p.zHom C.tensorUnit = C.comp (C.rightUnitorHom p.object) p.hom := by
  unfold PiData.zHom
  rw [unitors_hom_equal hC, hC.right_unitor_naturality]

theorem rightZ_unit : p.rightZHom C.tensorUnit = C.comp (C.leftUnitorHom p.object) p.hom := by
  unfold PiData.rightZHom
  rw [← unitors_hom_equal hC, hC.left_unitor_naturality]

include hp

theorem central_unit : p.centralHom C.tensorUnit =
    C.comp (C.rightUnitorHom p.object) (C.leftUnitorInv p.object) := by
  have he : C.comp (p.centralHom C.tensorUnit) (p.rightZHom C.tensorUnit) =
      C.comp (C.comp (C.rightUnitorHom p.object) (C.leftUnitorInv p.object))
        (p.rightZHom C.tensorUnit) := by
    rw [hp.central_rightZ hC, z_unit hC, rightZ_unit hC, hC.comp_assoc,
      ← hC.comp_assoc (C.leftUnitorInv p.object), hC.left_unitor_inv_hom, hC.id_comp]
  have he' := congrArg (fun f => C.comp f (p.rightZInv C.tensorUnit)) he
  simpa only [hC.comp_assoc, (hp.rightZ_iso hC C.tensorUnit).hom_inv, hC.comp_id] using he'

end RMod.Classification.PiLaws
