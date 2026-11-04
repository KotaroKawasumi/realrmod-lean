import RMod.BrundanEllis.StackingKaroubiOrdinary
import RMod.BrundanEllis.StackingKaroubiCoherence

/-! Composition with an ordinary corner morphism is the restriction of ambient
composition with its underlying map. These full Hom equations let monoidal
naturality descend through the concrete corner inclusions. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable {C : Type} [SuperCategory C]

@[reassoc] theorem whisker_post_inclusion (P : Karoubi (Even C))
    {Q R : Karoubi (Even C)} (f : Q ⟶ R) :
    eHomWhiskerLeft SuperVec P f ≫ inclusion P R =
      inclusion P Q ≫ eHomWhiskerLeft SuperVec P.X f.f := by
  change ((ρ_ (homObject P Q)).inv ≫ _ ◁ homPoint f ≫ composition P Q R) ≫ inclusion P R = _
  simp only [assoc, composition_inclusion, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
    Category.id_comp, homPoint_inclusion]
  rw [eHomWhiskerLeft, rightUnitor_inv_naturality_assoc]
  simp only [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
    Category.id_comp, Category.comp_id]

@[reassoc] theorem whisker_pre_inclusion {P Q : Karoubi (Even C)} (f : P ⟶ Q)
    (R : Karoubi (Even C)) :
    eHomWhiskerRight SuperVec f R ≫ inclusion P R =
      inclusion Q R ≫ eHomWhiskerRight SuperVec f.f R.X := by
  change ((λ_ (homObject Q R)).inv ≫ homPoint f ▷ _ ≫ composition P Q R) ≫ inclusion P R = _
  simp only [assoc, composition_inclusion, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
    Category.id_comp, homPoint_inclusion]
  rw [eHomWhiskerRight, leftUnitor_inv_naturality_assoc]
  simp only [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
    Category.id_comp, Category.comp_id]

/-- A restricted map acts on a corner exactly as its ambient map. -/
@[reassoc] theorem cut_post_inclusion [MonoidalCategory (Even C)] (R : Karoubi (Even C))
    {P Q : Karoubi (Even C)} (f : P.X ⟶ Q.X) (h : P.p ≫ f = f ≫ Q.p) :
    eHomWhiskerLeft SuperVec R (KaroubiTensor.cut f h) ≫ inclusion R Q =
      inclusion R P ≫ eHomWhiskerLeft SuperVec R.X f := by
  rw [whisker_post_inclusion, KaroubiTensor.cut_f, eHomWhiskerLeft_comp,
    ← assoc, inclusion_post]

@[reassoc] theorem cut_pre_inclusion [MonoidalCategory (Even C)] {P Q : Karoubi (Even C)}
    (f : P.X ⟶ Q.X) (h : P.p ≫ f = f ≫ Q.p) (R : Karoubi (Even C)) :
    eHomWhiskerRight SuperVec (KaroubiTensor.cut f h) R ≫ inclusion P R =
      inclusion Q R ≫ eHomWhiskerRight SuperVec f R.X := by
  rw [whisker_pre_inclusion, KaroubiTensor.cut_f, h, eHomWhiskerRight_comp,
    ← assoc, inclusion_pre]

/-- Transporting a Hom corner along object equality commutes with its inclusion. -/
theorem inclusion_transport {P P' Q Q' : Karoubi (Even C)} (hP : P = P') (hQ : Q = Q') :
    eqToHom (congrArg₂ homObject hP hQ) ≫ inclusion P' Q' =
      inclusion P Q ≫ eqToHom (congrArg₂ (fun X Y : Even C => X ⟶[SuperVec] Y)
        (congrArg Karoubi.X hP) (congrArg Karoubi.X hQ)) := by
  subst hP
  subst hQ
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

end RMod.BrundanEllis.Stacking.KaroubiSuper
