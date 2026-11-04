import RMod.Classification.Instances.ConvolutionUnitorsOfParity
import Batteries.Tactic.GeneralizeProofs

/-!
# The surviving convolution unit blocks as specified equality transports

The group indices, supported unit, and parity-zero factor identify the
surviving summand with the ordinary double-unit tensor. The remaining
map is the composite of the two ambient unitors.
-/

set_option autoImplicit false

namespace RMod.Classification

attribute [local implicit_reducible] convolutionEvenFamily twistSummand

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

theorem convolutionLeftUnitBlockOfParity_hom (hν : ∀ g : t.group, t.nu 1 g = 0)
    (X : PullbackObj C t) (k : t.group)
    (hs : twistSummand C t (pullbackUnitObj C hC t) X 1 (1⁻¹ * k) =
      C.tensorObj (C.tensorObj C.tensorUnit (X k).val) C.tensorUnit) :
    (convolutionLeftUnitBlockOfParity C hC t hν X k).hom.hom =
      C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData hs).hom
        (C.comp (C.rightUnitorHom (C.tensorObj C.tensorUnit (X k).val)) (C.leftUnitorHom (X k).val)) := by
  dsimp only [convolutionLeftUnitBlockOfParity]
  generalize_proofs hC₀ hm h₁ h₂ h₃ h₄
  revert h₁ h₂ h₃ h₄ hs
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
  have ha' : a = 0 := ha.symm.trans (hν k)
  clear ha
  subst a
  generalize hU : (pullbackUnitObj C hC t 1).val = U
  have hU' : U = C.tensorUnit := by rw [← hU, pullbackUnitObj, supportedObj_one]
  clear hU
  subst U
  intros
  change C.comp (C.rightUnitorHom (C.tensorObj C.tensorUnit (X k).val)) (C.leftUnitorHom (X k).val) = C.comp (C.id _) (C.comp (C.rightUnitorHom (C.tensorObj C.tensorUnit (X k).val)) (C.leftUnitorHom (X k).val))
  exact (hC.id_comp _).symm

theorem convolutionRightUnitBlockOfParity_hom (hν : ∀ g : t.group, t.nu g 1 = 0)
    (X : PullbackObj C t) (k : t.group)
    (hs : twistSummand C t X (pullbackUnitObj C hC t) k (k⁻¹ * k) =
      C.tensorObj (C.tensorObj (X k).val C.tensorUnit) C.tensorUnit) :
    (convolutionRightUnitBlockOfParity C hC t hν X k).hom.hom =
      C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData hs).hom
        (C.comp (C.rightUnitorHom (C.tensorObj (X k).val C.tensorUnit)) (C.rightUnitorHom (X k).val)) := by
  dsimp only [convolutionRightUnitBlockOfParity]
  generalize_proofs hC₀ hm h₁ h₂ h₃
  revert h₁ h₂ h₃ hs
  dsimp only [convolutionEvenFamily, twistSummand]
  generalize he : k⁻¹ * k = e
  have he' : e = 1 := he.symm.trans (inv_mul_cancel k)
  clear he
  subst e
  generalize ha : t.nu k 1 = a
  have ha' : a = 0 := ha.symm.trans (hν k)
  clear ha
  subst a
  generalize hU : (pullbackUnitObj C hC t 1).val = U
  have hU' : U = C.tensorUnit := by rw [← hU, pullbackUnitObj, supportedObj_one]
  clear hU
  subst U
  intros
  change C.comp (C.rightUnitorHom (C.tensorObj (X k).val C.tensorUnit)) (C.rightUnitorHom (X k).val) = C.comp (C.id _) (C.comp (C.rightUnitorHom (C.tensorObj (X k).val C.tensorUnit)) (C.rightUnitorHom (X k).val))
  exact (hC.id_comp _).symm

end RMod.Classification
