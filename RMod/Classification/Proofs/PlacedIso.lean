import RMod.Classification.Proofs.ComponentPlacement
import RMod.Classification.Instances.ConvolutionMonoidal

/-!
# Placing homogeneous isomorphisms and nonzero identities

Placement retains the original maps at the support and extends by zero.
Its composition and identity equations give homogeneous isomorphisms in
the completed monoidal supercategory interface of convolution.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion.Category

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)
  (g : t.group) {X Y : C.Obj}
  (hX : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g)) X)
  (hY : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g)) Y)

theorem placed_homogeneous_iso {a : ZMod 2}
    (h : C.HasHomogeneousIso a X Y) :
    Nonempty (HomogeneousIso ℝ (C := ConvolutionCategory C hC t ht) a
      (placedObj C hC t g X hX) (placedObj C hC t g Y hY)) := by
  obtain ⟨f, j, hfj, hjf, hf, hj⟩ := h
  refine ⟨⟨⟨placedHom C hC t g hX hY f, placedHom C hC t g hY hX j, ?_, ?_⟩,
    placedHom_grade C hC t g hX hY f hf, placedHom_grade C hC t g hY hX j hj⟩⟩
  · funext k
    change C.comp (placedHom C hC t g hX hY f k) (placedHom C hC t g hY hX j k) = _
    rw [placedHom_comp, hfj, placedHom_id]
    rfl
  · funext k
    change C.comp (placedHom C hC t g hY hX j k) (placedHom C hC t g hX hY f k) = _
    rw [placedHom_comp, hjf, placedHom_id]
    rfl

theorem placed_id_ne_zero (hne : C.id X ≠ C.zero) :
    @CategoryStruct.id (ConvolutionCategory C hC t ht) _ (placedObj C hC t g X hX) ≠ 0 := by
  intro he
  have hh := congrFun he g
  change C.id (placedObj C hC t g X hX g).val = C.zero at hh
  rw [placedObj_at] at hh
  exact hne hh

end RMod.Classification
