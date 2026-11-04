import RMod.Classification.Proofs.IsoNaturality
import RMod.Classification.Proofs.StructuralCoherence

/-!
# Compatibility of the two unit insertions

For an object equipped with an even isomorphism from the unit, inserting
that isomorphism on the left or the right gives the same map into its
tensor square. Naturality reduces both expressions to the tensor square
of the specified map; ordinary unit coherence identifies the remaining
unitors. The comparison retains its specified scalar normalization.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

variable {C : WeaklyPointedSuperfusionData.{u, v}} (hC : WeaklyPointedSuperfusionLaws C)

include hC

theorem unitors_inv_equal : C.leftUnitorInv C.tensorUnit = C.rightUnitorInv C.tensorUnit := by
  calc
    _ = C.comp (C.comp (C.leftUnitorInv C.tensorUnit) (C.rightUnitorHom C.tensorUnit))
        (C.rightUnitorInv C.tensorUnit) := by
      rw [hC.comp_assoc, hC.right_unitor_hom_inv, hC.comp_id]
    _ = _ := by rw [← unitors_hom_equal hC, hC.left_unitor_inv_hom, hC.id_comp]

theorem unit_insertions_equal {X : C.Obj} {i : IsoData C C.tensorUnit X}
    (hi : EvenIsoLaws C i) :
    C.comp (C.leftUnitorInv X) (C.tensorHom i.hom (C.id X)) =
      C.comp (C.rightUnitorInv X) (C.tensorHom (C.id X) i.hom) := by
  have hl := iso_naturality_symm hC (EvenIsoLaws.leftUnit hC C.tensorUnit).toIsoLaws
    (EvenIsoLaws.leftUnit hC X).toIsoLaws (hC.left_unitor_naturality i.hom)
  have hr := iso_naturality_symm hC (EvenIsoLaws.rightUnit hC C.tensorUnit).toIsoLaws
    (EvenIsoLaws.rightUnit hC X).toIsoLaws (hC.right_unitor_naturality i.hom)
  change C.comp i.hom (C.leftUnitorInv X) =
    C.comp (C.leftUnitorInv C.tensorUnit) (C.tensorHom (C.id C.tensorUnit) i.hom) at hl
  change C.comp i.hom (C.rightUnitorInv X) =
    C.comp (C.rightUnitorInv C.tensorUnit) (C.tensorHom i.hom (C.id C.tensorUnit)) at hr
  have he : C.comp i.hom (C.comp (C.leftUnitorInv X) (C.tensorHom i.hom (C.id X))) =
      C.comp i.hom (C.comp (C.rightUnitorInv X) (C.tensorHom (C.id X) i.hom)) := by
    rw [← hC.comp_assoc, hl, hC.comp_assoc,
      interchange_first_even hC _ _ _ _ (hC.id_even C.tensorUnit), hC.id_comp, hC.comp_id]
    rw [← hC.comp_assoc i.hom, hr, hC.comp_assoc,
      interchange_second_even hC _ _ _ _ hi.hom_even, hC.id_comp, hC.comp_id, unitors_inv_equal hC]
  have h := congrArg (C.comp i.inv) he
  simpa only [← hC.comp_assoc i.inv i.hom, hi.inv_hom, hC.id_comp] using h

end RMod.Classification
