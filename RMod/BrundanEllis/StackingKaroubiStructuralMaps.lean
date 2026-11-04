import RMod.BrundanEllis.StackingKaroubiEvenMaps

/-! The completed associator and unitors act on full Hom corners as the
ambient structural maps. The source and target idempotents disappear because
Hom inclusions are already fixed by both projectors. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable {C : Type} [SuperCategory C] [MonoidalCategory (Even C)]

abbrev baseObject (P : Even (Karoubi (Even C))) : Even C := (ForgetEnrichment.to SuperVec P).X

@[simp] theorem baseObject_tensor (P Q : Even (Karoubi (Even C))) :
    baseObject (P ⊗ Q) = baseObject P ⊗ baseObject Q := rfl
@[simp] theorem baseObject_unit : baseObject (𝟙_ (Even (Karoubi (Even C)))) = 𝟙_ (Even C) := rfl

@[reassoc] theorem associator_post (W P Q R : Even (Karoubi (Even C))) :
    eHomWhiskerLeft SuperVec W (α_ P Q R).hom ≫ evenInclusion W (P ⊗ (Q ⊗ R)) =
    evenInclusion W ((P ⊗ Q) ⊗ R) ≫
      eHomWhiskerLeft SuperVec (baseObject W) (α_ (baseObject P) (baseObject Q) (baseObject R)).hom := by
  let w := ForgetEnrichment.to SuperVec W
  let p := ForgetEnrichment.to SuperVec P
  let q := ForgetEnrichment.to SuperVec Q
  let r := ForgetEnrichment.to SuperVec R
  rw [even_whisker_post, even_associator_map]
  change eHomWhiskerLeft SuperVec w (KaroubiTensor.associator p q r).hom ≫ inclusion w (p ⊗ (q ⊗ r)) =
    inclusion w ((p ⊗ q) ⊗ r) ≫ eHomWhiskerLeft SuperVec w.X (α_ p.X q.X r.X).hom
  rw [KaroubiTensor.associator_hom_cut]
  exact cut_post_inclusion w _ _

@[reassoc] theorem associator_pre (P Q R W : Even (Karoubi (Even C))) :
    eHomWhiskerRight SuperVec (α_ P Q R).hom W ≫ evenInclusion ((P ⊗ Q) ⊗ R) W =
    evenInclusion (P ⊗ (Q ⊗ R)) W ≫
      eHomWhiskerRight SuperVec (α_ (baseObject P) (baseObject Q) (baseObject R)).hom (baseObject W) := by
  let w := ForgetEnrichment.to SuperVec W
  let p := ForgetEnrichment.to SuperVec P
  let q := ForgetEnrichment.to SuperVec Q
  let r := ForgetEnrichment.to SuperVec R
  rw [even_whisker_pre, even_associator_map]
  change eHomWhiskerRight SuperVec (KaroubiTensor.associator p q r).hom w ≫ inclusion ((p ⊗ q) ⊗ r) w =
    inclusion (p ⊗ (q ⊗ r)) w ≫ eHomWhiskerRight SuperVec (α_ p.X q.X r.X).hom w.X
  rw [KaroubiTensor.associator_hom_cut]
  exact cut_pre_inclusion _ _ w

@[reassoc] theorem leftUnitor_post (W P : Even (Karoubi (Even C))) :
    eHomWhiskerLeft SuperVec W (λ_ P).hom ≫ evenInclusion W P =
    evenInclusion W ((𝟙_ _) ⊗ P) ≫ eHomWhiskerLeft SuperVec (baseObject W) (λ_ (baseObject P)).hom := by
  let w := ForgetEnrichment.to SuperVec W
  let p := ForgetEnrichment.to SuperVec P
  rw [even_whisker_post, even_leftUnitor_map]
  change eHomWhiskerLeft SuperVec w (KaroubiTensor.leftUnitor p).hom ≫ inclusion w p =
    inclusion w ((𝟙_ (Karoubi (Even C))) ⊗ p) ≫ eHomWhiskerLeft SuperVec w.X (λ_ p.X).hom
  rw [KaroubiTensor.leftUnitor_hom_cut]
  exact cut_post_inclusion w _ _

@[reassoc] theorem leftUnitor_pre (P W : Even (Karoubi (Even C))) :
    eHomWhiskerRight SuperVec (λ_ P).hom W ≫ evenInclusion ((𝟙_ _) ⊗ P) W =
    evenInclusion P W ≫ eHomWhiskerRight SuperVec (λ_ (baseObject P)).hom (baseObject W) := by
  let w := ForgetEnrichment.to SuperVec W
  let p := ForgetEnrichment.to SuperVec P
  rw [even_whisker_pre, even_leftUnitor_map]
  change eHomWhiskerRight SuperVec (KaroubiTensor.leftUnitor p).hom w ≫ inclusion ((𝟙_ (Karoubi (Even C))) ⊗ p) w =
    inclusion p w ≫ eHomWhiskerRight SuperVec (λ_ p.X).hom w.X
  rw [KaroubiTensor.leftUnitor_hom_cut]
  exact cut_pre_inclusion _ _ w

@[reassoc] theorem rightUnitor_post (W P : Even (Karoubi (Even C))) :
    eHomWhiskerLeft SuperVec W (ρ_ P).hom ≫ evenInclusion W P =
    evenInclusion W (P ⊗ (𝟙_ _)) ≫ eHomWhiskerLeft SuperVec (baseObject W) (ρ_ (baseObject P)).hom := by
  let w := ForgetEnrichment.to SuperVec W
  let p := ForgetEnrichment.to SuperVec P
  rw [even_whisker_post, even_rightUnitor_map]
  change eHomWhiskerLeft SuperVec w (KaroubiTensor.rightUnitor p).hom ≫ inclusion w p =
    inclusion w (p ⊗ (𝟙_ (Karoubi (Even C)))) ≫ eHomWhiskerLeft SuperVec w.X (ρ_ p.X).hom
  rw [KaroubiTensor.rightUnitor_hom_cut]
  exact cut_post_inclusion w _ _

@[reassoc] theorem rightUnitor_pre (P W : Even (Karoubi (Even C))) :
    eHomWhiskerRight SuperVec (ρ_ P).hom W ≫ evenInclusion (P ⊗ (𝟙_ _)) W =
    evenInclusion P W ≫ eHomWhiskerRight SuperVec (ρ_ (baseObject P)).hom (baseObject W) := by
  let w := ForgetEnrichment.to SuperVec W
  let p := ForgetEnrichment.to SuperVec P
  rw [even_whisker_pre, even_rightUnitor_map]
  change eHomWhiskerRight SuperVec (KaroubiTensor.rightUnitor p).hom w ≫ inclusion (p ⊗ (𝟙_ (Karoubi (Even C)))) w =
    inclusion p w ≫ eHomWhiskerRight SuperVec (ρ_ p.X).hom w.X
  rw [KaroubiTensor.rightUnitor_hom_cut]
  exact cut_pre_inclusion _ _ w

end RMod.BrundanEllis.Stacking.KaroubiSuper
