import RMod.Classification.Instances.PlacedDualSnakeBlock
import RMod.Classification.Proofs.PlacedDualInsertions
import RMod.Classification.Proofs.NormalizedDualSnake

/-!
# Reduction of the surviving block to the local weighted snake

The inverse group products become the identity, the adjacent parity
entries vanish, and the two inverse-pair parities agree. Equality
transport then leaves precisely the normalized local snake.
-/

set_option autoImplicit false

namespace RMod.Classification

attribute [local implicit_reducible] twistSummand convolutionLeftFamily convolutionRightFamily
  convolutionEvenFamily

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)
  (g : t.group) {X Y : C.Obj}
  (hX : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g)) X)
  (q : DualPairing ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩ X Y)

theorem placedFirstSnakeBlock_eq_id : placedFirstSnakeBlock C hC t ht g hX q =
    C.id (placedObj C hC t g X hX g).val := by
  classical
  dsimp only [placedFirstSnakeBlock, convolutionInversePairBlock, convolutionBlockIso, convolutionBlockIsoOfParity,
    convolutionLeftUnitBlock, convolutionLeftUnitBlockOfParity, convolutionRightUnitBlock, convolutionRightUnitBlockOfParity, placedCoevaluationBlock]
  generalize_proofs hC₀ hm hm' l₁ l₂ l₃ l₄ hmC hη hi ho hin he hlaw r₁ r₂ r₃
  revert l₁ l₂ l₃ l₄ hη hi ho hin he hlaw r₁ r₂ r₃
  dsimp only [convolutionLeftFamily, convolutionRightFamily, convolutionEvenFamily, twistSummand]
  generalize hx : g * g⁻¹ = a
  have hx' : a = 1 := hx.symm.trans (mul_inv_cancel g)
  clear hx
  subst a
  generalize hx : g⁻¹ * g = a
  have hx' : a = 1 := hx.symm.trans (inv_mul_cancel g)
  clear hx
  subst a
  intro l₁ l₂ l₃ l₄ hη hi ho hin he hlaw r₁ r₂ r₃
  rw [placedTwistedEvaluation_inclusion]
  dsimp only [placedEvaluationBlock, twistSummand]
  generalize_proofs hε
  revert l₁ l₂ l₃ l₄ hη hi ho hin he hlaw r₁ r₂ r₃ hε
  generalize hx : g⁻¹ * g = a
  have hx' : a = 1 := hx.symm.trans (inv_mul_cancel g)
  clear hx
  subst a
  generalize hx : (1 : t.group)⁻¹ * g = a
  have hx' : a = g := by rw [← hx, inv_one, one_mul]
  clear hx
  subst a
  generalize hx : g⁻¹⁻¹ = a
  have hx' : a = g := hx.symm.trans (inv_inv g)
  clear hx
  subst a
  generalize hx : (1 : t.group) * g = a
  have hx' : a = g := hx.symm.trans (one_mul g)
  clear hx
  subst a
  generalize hx : g * (1 : t.group) = a
  have hx' : a = g := hx.symm.trans (mul_one g)
  clear hx
  subst a
  generalize hx : g⁻¹ * (1 : t.group) = a
  have hx' : a = g⁻¹ := hx.symm.trans (mul_one g⁻¹)
  clear hx
  subst a
  generalize hx : t.nu 1 g = a
  have hx' : a = 0 := hx.symm.trans (ht.nu_one_left g)
  clear hx
  subst a
  generalize hx : t.nu g 1 = a
  have hx' : a = 0 := hx.symm.trans (ht.nu_one_right g)
  clear hx
  subst a
  generalize hx : t.nu g⁻¹ g = a
  have hx' : a = t.nu g g⁻¹ := hx.symm.trans (ht.inverse_parity g).symm
  clear hx
  subst a
  generalize hx : t.nu g (g⁻¹ * g) = a
  have hx' : a = 0 := by rw [← hx, inv_mul_cancel, ht.nu_one_right]
  clear hx
  subst a
  dsimp only [placedRightDualObj, placedObj, pullbackUnitObj, supportedObj]
  generalize hx : (if g = g then X else (pullbackZeroObj C hC t g).val) = A
  have hx' : A = X := hx.symm.trans (if_pos rfl)
  clear hx
  subst A
  generalize hy : (if g⁻¹ = g⁻¹ then C.tensorObj Y (C.pi.factor (t.nu g g⁻¹))
    else (pullbackZeroObj C hC t g⁻¹).val) = B
  have hy' : B = C.tensorObj Y (C.pi.factor (t.nu g g⁻¹)) := by
    exact hy.symm.trans (if_pos rfl)
  clear hy
  subst B
  generalize hu : (if (1 : t.group) = 1 then C.tensorUnit else (pullbackZeroObj C hC t 1).val) = U
  have hu' : U = C.tensorUnit := hu.symm.trans (if_pos rfl)
  clear hu
  subst U
  intros
  simp only [CategoryTheory.eqToIso_refl, CategoryTheory.Iso.refl_trans]
  change C.comp
    (C.comp (C.leftUnitorInv X) (C.rightUnitorInv (C.tensorObj C.tensorUnit X)))
    (C.comp
      (C.tensorHom (C.tensorHom (C.pi.twistedCoevaluation q.data (t.nu g g⁻¹)) (C.id X))
        (C.id C.tensorUnit))
      (C.comp (C.pi.localAssociator X (C.tensorObj Y (C.pi.factor (t.nu g g⁻¹))) X
        (t.nu g g⁻¹) 0 (t.nu g g⁻¹) 0 rfl (t.omega g g⁻¹ g)).hom
        (C.comp
          (C.tensorHom (C.tensorHom (C.id X)
            (C.pi.twistedEvaluation q.data (t.nu g g⁻¹) (t.omega g g⁻¹ g))) (C.id C.tensorUnit))
          (C.comp (C.rightUnitorHom (C.tensorObj X C.tensorUnit)) (C.rightUnitorHom X))))) = C.id X
  simpa only [hC.comp_assoc] using normalizedLocal_first_snake
    ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩ C.pi hC.pi q
    (t.nu g g⁻¹) (t.omega g g⁻¹ g)

end RMod.Classification
