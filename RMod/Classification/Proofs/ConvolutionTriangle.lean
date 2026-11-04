import RMod.Classification.Proofs.ConvolutionNaturality
import RMod.Classification.Proofs.ConvolutionUnitNaturality
import RMod.Classification.Proofs.ConvolutionPartialMaps
import RMod.Classification.Proofs.ParityTriangle

/-!
# The triangle on the actual convolution objects

Only the identity coordinate of the middle unit can contribute to a
threefold summand. On that coordinate the specified omega is one and the
adjacent parity factors vanish, so the exact local triangle applies.
-/

set_option autoImplicit false

namespace RMod.Classification

attribute [local implicit_reducible] twistSummand convolutionLeftFamily convolutionRightFamily
  convolutionEvenFamily

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (ht : TwistLaws t)

theorem convolutionTriangle_unit_summand (X Y : PullbackObj C t) (k a : t.group) :
    C.comp (convolutionLeftInsertionEven C hC t X (pullbackUnitObj C hC t) Y k (a * 1) a).hom
      (C.comp (convolutionAssociatorData C hC t ht X (pullbackUnitObj C hC t) Y k).hom
        (convolutionHom C hC t (fun g => C.id (X g).val)
          (fun g => (convolutionLeftUnitorData C hC t ht Y g).hom) k)) =
    C.comp (convolutionLeftInsertionEven C hC t X (pullbackUnitObj C hC t) Y k (a * 1) a).hom
      (convolutionHom C hC t (fun g => (convolutionRightUnitorData C hC t ht X g).hom)
        (fun g => C.id (Y g).val) k) := by
  rw [← hC.comp_assoc, convolutionAssociator_inclusion_hom, hC.comp_assoc,
    convolutionRightInsertion_outer_map, convolutionLeftInsertion_outer_map,
    convolutionLeftUnitor_inclusion]
  dsimp only [convolutionBlockIso, convolutionBlockIsoOfParity]
  generalize_proofs hC₀ hm hm' hout hin he hlaw
  revert hout hin he hlaw
  dsimp only [convolutionLeftFamily, convolutionRightFamily, convolutionEvenFamily, twistSummand]
  generalize ha : a * 1 = aa
  have ha' : aa = a := ha.symm.trans (mul_one a)
  clear ha
  subst aa
  intro hout hin he hlaw
  rw [convolutionRightUnitor_inclusion]
  dsimp only [convolutionLeftUnitBlock, convolutionLeftUnitBlockOfParity, convolutionRightUnitBlock, convolutionRightUnitBlockOfParity]
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
  have ha' : aa = 0 := ha.symm.trans (ht.nu_one_right a)
  clear ha
  subst aa
  generalize ha : t.nu 1 (a⁻¹ * k) = aa
  have ha' : aa = 0 := ha.symm.trans (ht.nu_one_left _)
  clear ha
  subst aa
  generalize hU : (pullbackUnitObj C hC t 1).val = U
  have hU' : U = C.tensorUnit := by rw [← hU, pullbackUnitObj, supportedObj_one]
  clear hU
  subst U
  simp only [ht.omega_one₂]
  intros
  have hl := localAssociator_triangle
    (⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩ : WeaklyPointedSuperfusion)
    C.pi hC.pi (X a).val (Y (a⁻¹ * k)).val (t.nu a (a⁻¹ * k))
  have he := congrArg (fun m => C.comp m (convolutionInclusion C hC t X Y k a)) hl
  rw [hC.comp_assoc] at he
  exact he

/-- A nonidentity coordinate of the middle unit makes the whole source zero. -/
theorem convolutionLeftUnitFamily_id_zero (X Y : PullbackObj C t) (k a b : t.group)
    (hb : b ≠ 1) :
    C.id (convolutionLeftFamily C hC t X (pullbackUnitObj C hC t) Y k (a * b) a).obj = C.zero := by
  have hu := pullbackUnit_id_zero C hC t (a⁻¹ * (a * b))
    (by simpa only [inv_mul_cancel_left] using hb)
  exact tensor_id_zero_left hC.toWeaklyPointedSuperfusionLaws
    (tensor_id_zero_left hC.toWeaklyPointedSuperfusionLaws
      (tensor_id_zero_left hC.toWeaklyPointedSuperfusionLaws
        (tensor_id_zero_right hC.toWeaklyPointedSuperfusionLaws (X a).val hu) _) _) _

theorem convolution_triangle (X Y : PullbackObj C t) (k : t.group) :
    C.comp (convolutionAssociatorData C hC t ht X (pullbackUnitObj C hC t) Y k).hom
      (convolutionHom C hC t (fun g => C.id (X g).val)
        (fun g => (convolutionLeftUnitorData C hC t ht Y g).hom) k) =
    convolutionHom C hC t (fun g => (convolutionRightUnitorData C hC t ht X g).hom)
      (fun g => C.id (Y g).val) k := by
  apply hom_ext_of_convolutionLeftInsertions_pairs C hC t X (pullbackUnitObj C hC t) Y k
  intro a b
  by_cases hb : b = 1
  · subst b
    exact convolutionTriangle_unit_summand C hC t ht X Y k a
  · have hz := convolutionLeftUnitFamily_id_zero C hC t X Y k a b hb
    exact (hom_eq_zero_of_source hC.toWeaklyPointedSuperfusionLaws hz _).trans
      (hom_eq_zero_of_source hC.toWeaklyPointedSuperfusionLaws hz _).symm

theorem twistedPullback_triangle (X Y : (twistedPullbackData C hC t ht).Obj) :
    let D := twistedPullbackData C hC t ht
    D.comp (D.associatorHom X D.tensorUnit Y) (D.whiskerLeft X (D.leftUnitorHom Y)) =
      D.whiskerRight (D.rightUnitorHom X) Y := by
  funext k
  exact convolution_triangle C hC t ht X Y k

end RMod.Classification
