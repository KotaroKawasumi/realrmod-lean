import RMod.BrundanEllis.StackingKaroubiEnrichment

/-! The degree-zero morphisms of the enriched completion are precisely the
usual Karoubi morphisms. This identifies its even category with Mathlib's
ordinary idempotent completion without any new existence hypotheses. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable {C : Type} [SuperCategory C]

def homPoint {P Q : Karoubi (Even C)} (f : P ⟶ Q) :
    𝟙_ SuperVec ⟶ homObject P Q := eHomEquiv SuperVec f.f ≫ restriction P Q

@[reassoc] theorem homPoint_inclusion {P Q : Karoubi (Even C)} (f : P ⟶ Q) :
    homPoint f ≫ inclusion P Q = eHomEquiv SuperVec f.f := by
  simp only [homPoint, assoc, restriction_inclusion, projector]
  rw [← assoc, even_pre, Karoubi.p_comp, even_post, Karoubi.comp_p]

def pointHom {P Q : Karoubi (Even C)} (f : 𝟙_ SuperVec ⟶ homObject P Q) : P ⟶ Q where
  f := (eHomEquiv SuperVec).symm (f ≫ inclusion P Q)
  comm := by
    apply (eHomEquiv SuperVec).injective
    rw [← assoc, ← even_post, ← even_pre, Equiv.apply_symm_apply]
    simp only [assoc, inclusion_pre, inclusion_post]

def homEquivalence (P Q : Karoubi (Even C)) :
    (P ⟶ Q) ≃ (𝟙_ SuperVec ⟶ homObject P Q) where
  toFun := homPoint
  invFun := pointHom
  left_inv f := by
    apply Karoubi.hom_ext
    change (eHomEquiv SuperVec).symm (homPoint f ≫ inclusion P Q) = f.f
    rw [homPoint_inclusion, Equiv.symm_apply_apply]
  right_inv f := by
    apply (cancel_mono (inclusion P Q)).1
    rw [homPoint_inclusion]
    exact Equiv.apply_symm_apply _ _

instance ordinaryEnrichment : EnrichedOrdinaryCategory SuperVec (Karoubi (Even C)) where
  toEnrichedCategory := enrichment
  homEquiv := homEquivalence _ _
  homEquiv_id P := rfl
  homEquiv_comp {P Q R} f g := by
    apply (cancel_mono (inclusion P R)).1
    change homPoint (f ≫ g) ≫ inclusion P R =
      ((λ_ (𝟙_ SuperVec)).inv ≫ (homPoint f ⊗ₘ homPoint g) ≫ composition P Q R) ≫ inclusion P R
    simp only [assoc, homPoint_inclusion, composition_inclusion,
      tensorHom_comp_tensorHom_assoc, eHomEquiv_comp, Karoubi.comp_f]

/-- Canonical comparison with the ordinary Karoubi category. -/
def evenEquivalence : Even (Karoubi (Even C)) ≌ Karoubi (Even C) :=
  ForgetEnrichment.equiv SuperVec

end RMod.BrundanEllis.Stacking.KaroubiSuper
