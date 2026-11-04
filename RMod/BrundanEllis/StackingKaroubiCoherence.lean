import RMod.BrundanEllis.StackingKaroubiTensor

/-! Cutting maps that commute with the chosen idempotents respects
composition and tensor products. Coherence diagrams can therefore be cut
from the original diagrams before any target monoidal comparison is used. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiTensor
variable {C : Type} [Category C] [MonoidalCategory C]

/-- Restrict an idempotent-intertwining map to its two corners. -/
def cut {P Q : Karoubi C} (f : P.X ⟶ Q.X) (h : P.p ≫ f = f ≫ Q.p) : P ⟶ Q :=
  ⟨P.p ≫ f, by
    simp only [← Category.assoc, P.idem]
    rw [h, Category.assoc, Q.idem]⟩

@[simp] theorem cut_f {P Q : Karoubi C} (f : P.X ⟶ Q.X)
    (h : P.p ≫ f = f ≫ Q.p) : (cut f h).f = P.p ≫ f := rfl

@[simp] theorem cut_id (P : Karoubi C) :
    cut (𝟙 P.X) (by simp) = 𝟙 P := by ext; simp

@[simp] theorem cut_hom {P Q : Karoubi C} (f : P ⟶ Q) :
    cut f.f (Karoubi.p_comm f) = f := by ext; simp

@[simp] theorem cut_comp {P Q R : Karoubi C} (f : P.X ⟶ Q.X) (g : Q.X ⟶ R.X)
    (hf : P.p ≫ f = f ≫ Q.p) (hg : Q.p ≫ g = g ≫ R.p) :
    cut f hf ≫ cut g hg = cut (f ≫ g) (by
      rw [← Category.assoc, hf, Category.assoc, hg, ← Category.assoc]) := by
  apply Karoubi.hom_ext
  change (P.p ≫ f) ≫ Q.p ≫ g = P.p ≫ f ≫ g
  have hc : (P.p ≫ f) ≫ Q.p = P.p ≫ f := Karoubi.comp_p (cut f hf)
  rw [← Category.assoc, hc, Category.assoc]

@[simp] theorem cut_tensor {P P' Q Q' : Karoubi C} (f : P.X ⟶ P'.X) (g : Q.X ⟶ Q'.X)
    (hf : P.p ≫ f = f ≫ P'.p) (hg : Q.p ≫ g = g ≫ Q'.p) :
    mapTensor (cut f hf) (cut g hg) = cut (f ⊗ₘ g) (by
      change (P.p ⊗ₘ Q.p) ≫ (f ⊗ₘ g) = (f ⊗ₘ g) ≫ (P'.p ⊗ₘ Q'.p)
      rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, hf, hg]) := by
  apply Karoubi.hom_ext
  change (P.p ≫ f) ⊗ₘ (Q.p ≫ g) = (P.p ⊗ₘ Q.p) ≫ (f ⊗ₘ g)
  rw [tensorHom_comp_tensorHom]

@[simp] theorem associator_hom_cut (P Q R : Karoubi C) :
    (associator P Q R).hom = cut (α_ P.X Q.X R.X).hom
      (associator_naturality P.p Q.p R.p) := rfl

@[simp] theorem leftUnitor_hom_cut (P : Karoubi C) :
    (leftUnitor P).hom = cut (λ_ P.X).hom (by
      simpa only [objectTensor, Karoubi.coe_p, id_tensorHom] using leftUnitor_naturality P.p) := rfl

@[simp] theorem rightUnitor_hom_cut (P : Karoubi C) :
    (rightUnitor P).hom = cut (ρ_ P.X).hom (by
      simpa only [objectTensor, Karoubi.coe_p, tensorHom_id] using rightUnitor_naturality P.p) := rfl

end RMod.BrundanEllis.Stacking.KaroubiTensor
