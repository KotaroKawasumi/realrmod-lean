import RMod.Classification.Instances.ConvolutionUnitors
import RMod.Classification.Proofs.TensorCalculus
import Batteries.Tactic.GeneralizeProofs

/-!
# Naturality of the surviving unit blocks

Normalization of nu removes the parity factor. The supported unit is
then the original unit, and the two raw unitors are natural on the full
Hom space. Group-coordinate transports are dealt with before applying
these original naturality laws.
-/

set_option autoImplicit false

namespace RMod.Classification

attribute [local implicit_reducible] convolutionEvenFamily twistSummand

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (hνL : ∀ g : t.group, t.nu 1 g = 0) (hνR : ∀ g : t.group, t.nu g 1 = 0) {X Y : PullbackObj C t}

theorem convolutionLeftUnitBlockOfParity_naturality (f : PullbackHom C t X Y) (k : t.group) :
    C.comp (twistSummandHom C t (fun a => C.id (pullbackUnitObj C hC t a).val) f 1 (1⁻¹ * k))
      (convolutionLeftUnitBlockOfParity C hC t hνL Y k).hom.hom =
        C.comp (convolutionLeftUnitBlockOfParity C hC t hνL X k).hom.hom (f k) := by
  dsimp only [convolutionLeftUnitBlockOfParity, twistSummandHom]
  generalize_proofs hC₀ hm h₁ h₂ h₃ h₄ hs hm' h₅ h₆ h₇ h₈
  revert h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
  dsimp only [convolutionEvenFamily, twistSummand]
  generalize he : (1 : t.group)⁻¹ * k = e
  have he' : e = k := by rw [← he, inv_one, one_mul]
  clear he
  subst e
  generalize he : (1 : t.group) * k = e
  have he' : e = k := he.symm.trans (one_mul k)
  clear he
  subst e
  generalize ha : t.nu 1 k = a
  have ha' : a = 0 := ha.symm.trans (hνL k)
  clear ha
  subst a
  generalize hU : (pullbackUnitObj C hC t 1).val = U
  have hU' : U = C.tensorUnit := by rw [← hU, pullbackUnitObj, supportedObj_one]
  clear hU
  subst U
  intros
  change C.comp (C.tensorHom (C.tensorHom (C.id C.tensorUnit) (f k)) (C.id C.tensorUnit))
    (C.comp (C.rightUnitorHom (C.tensorObj C.tensorUnit (Y k).val)) (C.leftUnitorHom (Y k).val)) =
      C.comp (C.comp (C.rightUnitorHom (C.tensorObj C.tensorUnit (X k).val))
        (C.leftUnitorHom (X k).val)) (f k)
  rw [← hC.comp_assoc, hC.right_unitor_naturality, hC.comp_assoc,
    hC.left_unitor_naturality, ← hC.comp_assoc]

theorem convolutionRightUnitBlockOfParity_naturality (f : PullbackHom C t X Y) (k : t.group) :
    C.comp (twistSummandHom C t f (fun a => C.id (pullbackUnitObj C hC t a).val) k (k⁻¹ * k))
      (convolutionRightUnitBlockOfParity C hC t hνR Y k).hom.hom =
        C.comp (convolutionRightUnitBlockOfParity C hC t hνR X k).hom.hom (f k) := by
  dsimp only [convolutionRightUnitBlockOfParity, twistSummandHom]
  generalize_proofs hC₀ hm h₁ h₂ h₃ hs hm' h₄ h₅ h₆
  revert h₁ h₂ h₃ h₄ h₅ h₆
  dsimp only [convolutionEvenFamily, twistSummand]
  generalize he : k⁻¹ * k = e
  have he' : e = 1 := he.symm.trans (inv_mul_cancel k)
  clear he
  subst e
  generalize ha : t.nu k 1 = a
  have ha' : a = 0 := ha.symm.trans (hνR k)
  clear ha
  subst a
  generalize hU : (pullbackUnitObj C hC t 1).val = U
  have hU' : U = C.tensorUnit := by rw [← hU, pullbackUnitObj, supportedObj_one]
  clear hU
  subst U
  intros
  change C.comp (C.tensorHom (C.tensorHom (f k) (C.id C.tensorUnit)) (C.id C.tensorUnit))
    (C.comp (C.rightUnitorHom (C.tensorObj (Y k).val C.tensorUnit)) (C.rightUnitorHom (Y k).val)) =
      C.comp (C.comp (C.rightUnitorHom (C.tensorObj (X k).val C.tensorUnit))
        (C.rightUnitorHom (X k).val)) (f k)
  rw [← hC.comp_assoc, hC.right_unitor_naturality, hC.comp_assoc,
    hC.right_unitor_naturality, ← hC.comp_assoc]

theorem convolutionLeftUnitBlock_naturality (ht : TwistLaws t) (f : PullbackHom C t X Y) (k : t.group) :
    C.comp (twistSummandHom C t (fun a => C.id (pullbackUnitObj C hC t a).val) f 1 (1⁻¹ * k))
      (convolutionLeftUnitBlock C hC t ht Y k).hom.hom =
        C.comp (convolutionLeftUnitBlock C hC t ht X k).hom.hom (f k) :=
  convolutionLeftUnitBlockOfParity_naturality C hC t ht.nu_one_left f k

theorem convolutionRightUnitBlock_naturality (ht : TwistLaws t) (f : PullbackHom C t X Y) (k : t.group) :
    C.comp (twistSummandHom C t f (fun a => C.id (pullbackUnitObj C hC t a).val) k (k⁻¹ * k))
      (convolutionRightUnitBlock C hC t ht Y k).hom.hom =
        C.comp (convolutionRightUnitBlock C hC t ht X k).hom.hom (f k) :=
  convolutionRightUnitBlockOfParity_naturality C hC t ht.nu_one_right f k

end RMod.Classification
