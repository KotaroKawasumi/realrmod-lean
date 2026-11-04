import RMod.Classification.Proofs.ConvolutionBlocksOfParity
import RMod.Classification.Proofs.ConvolutionUnitInsertionsOfParity
import RMod.Classification.Proofs.ConvolutionPartialMaps
import RMod.Classification.Proofs.ParityTriangleNonvanishing

/-!
# The actual convolution triangle forces the middle scalar normalization

Restrict the triangle to the identity summand of its middle unit. After
normalizing the two zero parity factors, both sides end with the same
binary inclusion. Its specified projection cancels that inclusion and
the local scalar-faithfulness theorem forces omega to be one.
-/

set_option autoImplicit false

namespace RMod.Classification

attribute [local implicit_reducible] twistSummand convolutionLeftFamily convolutionRightFamily
  convolutionEvenFamily

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (hν : ∀ g h k : t.group, t.nu g h + t.nu (g * h) k = t.nu h k + t.nu g (h * k))
  (hνL : ∀ g : t.group, t.nu 1 g = 0) (hνR : ∀ g : t.group, t.nu g 1 = 0)

theorem convolutionTriangle_scalar_of_summand_eq (X Y : PullbackObj C t) (k a : t.group)
    (hX : C.id (X a).val ≠ C.zero) (hY : C.id (Y (a⁻¹ * k)).val ≠ C.zero)
    (heq : C.comp (convolutionLeftInsertionEven C hC t X (pullbackUnitObj C hC t) Y k (a * 1) a).hom
      (C.comp (convolutionAssociatorDataOfParity C hC t hν X (pullbackUnitObj C hC t) Y k).hom
        (convolutionHom C hC t (fun g => C.id (X g).val)
          (fun g => (convolutionLeftUnitorDataOfParity C hC t hνL Y g).hom) k)) =
    C.comp (convolutionLeftInsertionEven C hC t X (pullbackUnitObj C hC t) Y k (a * 1) a).hom
      (convolutionHom C hC t (fun g => (convolutionRightUnitorDataOfParity C hC t hνR X g).hom)
        (fun g => C.id (Y g).val) k)) : t.omega a 1 (a⁻¹ * k) = 1 := by
  rw [← hC.comp_assoc, convolutionAssociatorOfParity_inclusion_hom, hC.comp_assoc,
    convolutionRightInsertion_outer_map, convolutionLeftInsertion_outer_map,
    convolutionLeftUnitor_inclusionOfParity] at heq
  revert heq
  dsimp only [convolutionBlockIsoOfParity]
  generalize_proofs hC₀ hm hm' hout hin he hlaw
  revert hout hin he hlaw
  dsimp only [convolutionLeftFamily, convolutionRightFamily, convolutionEvenFamily, twistSummand]
  generalize ha : a * 1 = aa
  have ha' : aa = a := ha.symm.trans (mul_one a)
  clear ha
  subst aa
  intro hout hin he hlaw heq
  rw [convolutionRightUnitor_inclusionOfParity] at heq
  revert heq
  dsimp only [convolutionLeftUnitBlockOfParity, convolutionRightUnitBlockOfParity]
  generalize_proofs hl₁ hl₂ hl₃ hl₄ hs hr₁ hr₂ hr₃
  revert hout hin he hlaw hl₁ hl₂ hl₃ hl₄ hr₁ hr₂ hr₃
  dsimp only [convolutionEvenFamily, twistSummand]
  generalize ha : a⁻¹ * a = aa
  have ha' : aa = 1 := ha.symm.trans (inv_mul_cancel a)
  clear ha
  subst aa
  generalize hl : (1 : t.group)⁻¹ * (a⁻¹ * k) = l
  have hl' : l = a⁻¹ * k := by rw [← hl, inv_one, one_mul]
  clear hl
  subst l
  generalize hl : (1 : t.group) * (a⁻¹ * k) = l
  have hl' : l = a⁻¹ * k := hl.symm.trans (one_mul _)
  clear hl
  subst l
  generalize ha : t.nu a 1 = aa
  have ha' : aa = 0 := ha.symm.trans (hνR a)
  clear ha
  subst aa
  generalize ha : t.nu 1 (a⁻¹ * k) = aa
  have ha' : aa = 0 := ha.symm.trans (hνL _)
  clear ha
  subst aa
  generalize hU : (pullbackUnitObj C hC t 1).val = U
  have hU' : U = C.tensorUnit := by rw [← hU, pullbackUnitObj, supportedObj_one]
  clear hU
  subst U
  intro hout hin he hlaw hl₁ hl₂ hl₃ hl₄ hr₁ hr₂ hr₃ heq
  apply localAssociator_triangle_scalar_of_eq
    (⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩ : WeaklyPointedSuperfusion)
    C.pi hC.pi (X a).val (Y (a⁻¹ * k)).val (t.nu a (a⁻¹ * k)) _
    (parityTriangle_right_ne_zero
      ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩ C.pi hC.pi
      (X a).val (Y (a⁻¹ * k)).val (t.nu a (a⁻¹ * k)) hX hY)
  have hc := congrArg (fun m => C.comp m (convolutionProjection C hC t X Y k a)) heq
  simp only [hC.comp_assoc, convolutionInclusion_projection] at hc
  change C.comp
    (C.pi.localAssociator (X a).val C.tensorUnit (Y (a⁻¹ * k)).val 0 (t.nu a (a⁻¹ * k))
      0 (t.nu a (a⁻¹ * k)) rfl (t.omega a 1 (a⁻¹ * k))).hom
    (C.comp (C.tensorHom (C.tensorHom (C.id (X a).val)
      (C.comp (C.rightUnitorHom (C.tensorObj C.tensorUnit (Y (a⁻¹ * k)).val))
        (C.leftUnitorHom (Y (a⁻¹ * k)).val))) (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))
      (C.id _)) =
    C.comp (C.tensorHom (C.tensorHom
      (C.comp (C.rightUnitorHom (C.tensorObj (X a).val C.tensorUnit))
        (C.rightUnitorHom (X a).val)) (C.id (Y (a⁻¹ * k)).val))
      (C.id (C.pi.factor (t.nu a (a⁻¹ * k))))) (C.id _) at hc
  simpa only [hC.comp_id] using hc

end RMod.Classification
