import RMod.Classification.Instances.DualHomEquivalences
import RMod.Classification.Proofs.ConvolutionComponents

/-!
# Duality reverses the intrinsic component

The full real-linear dual Hom equivalences turn maps from a simple to a
dual into maps from a tensor product to the unit. Component orthogonality
then forces all unwanted simple components to vanish. This argument uses
the supplied pairing and the intrinsic reference property only.
-/

set_option autoImplicit false

namespace RMod.Classification.InComponent

open CategoryTheory

variable {C : PiSuperfusionData.{0, 0}} (hC : ReferenceProperty C)
  {X Y : C.Obj}
  (p : DualPairing ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩ X Y)

include hC p

/-- The right member of an exact pairing has the opposite component. -/
theorem right_dual {r : ZMod 8}
    (hX : InComponent C.toWeaklyPointedSuperfusionData r X) :
    InComponent C.toWeaklyPointedSuperfusionData (-r) Y := by
  apply (iff_orthogonal hC Y (-r)).mpr
  intro S s hS hs hsr f
  have hsum : s + r ≠ 0 := fun h => hsr (eq_neg_of_add_eq_zero_left h)
  let e := p.rightHomLinearEquiv S C.tensorUnit
  have hz : C.comp f (C.leftUnitorInv Y) = C.zero := by
    have hh := hom_zero hC (tensor hC (of_simple hC hS hs) hX) (tensor_unit hC)
      hsum (e.symm (C.comp f (C.leftUnitorInv Y)))
    change e.symm (C.comp f (C.leftUnitorInv Y)) = 0 at hh
    have he := congrArg e hh
    simp only [LinearEquiv.apply_symm_apply, map_zero] at he
    exact he
  calc
    f = C.comp (C.comp f (C.leftUnitorInv Y)) (C.leftUnitorHom Y) := by
      rw [hC.comp_assoc, hC.left_unitor_inv_hom, hC.comp_id]
    _ = C.zero := by rw [hz, raw_zero_comp hC.toWeaklyPointedSuperfusionLaws]

/-- The same conclusion holds for the left member, using the other adjunction. -/
theorem left_dual {r : ZMod 8}
    (hY : InComponent C.toWeaklyPointedSuperfusionData r Y) :
    InComponent C.toWeaklyPointedSuperfusionData (-r) X := by
  apply (iff_orthogonal hC X (-r)).mpr
  intro S s hS hs hsr f
  have hsum : r + s ≠ 0 := fun h => hsr (eq_neg_of_add_eq_zero_right h)
  let e := p.leftHomLinearEquiv S C.tensorUnit
  have hz : C.comp f (C.rightUnitorInv X) = C.zero := by
    have hh := hom_zero hC (tensor hC hY (of_simple hC hS hs)) (tensor_unit hC)
      hsum (e.symm (C.comp f (C.rightUnitorInv X)))
    change e.symm (C.comp f (C.rightUnitorInv X)) = 0 at hh
    have he := congrArg e hh
    simp only [LinearEquiv.apply_symm_apply, map_zero] at he
    exact he
  calc
    f = C.comp (C.comp f (C.rightUnitorInv X)) (C.rightUnitorHom X) := by
      rw [hC.comp_assoc, hC.right_unitor_inv_hom, hC.comp_id]
    _ = C.zero := by rw [hz, raw_zero_comp hC.toWeaklyPointedSuperfusionLaws]

end RMod.Classification.InComponent
