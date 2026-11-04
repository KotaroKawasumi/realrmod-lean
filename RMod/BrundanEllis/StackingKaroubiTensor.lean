import Mathlib.CategoryTheory.Idempotents.Karoubi
import Mathlib.CategoryTheory.Monoidal.Category

/-! Tensor products and structural isomorphisms of even idempotent corners.
These operations prepare the monoidal structure on the completion of an
ordinary monoidal category, without assuming a monoidal target functor. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiTensor
variable {C : Type} [Category C] [MonoidalCategory C]

/-- An ambient isomorphism that intertwines idempotents restricts to their corners. -/
def restrictIso {P Q : Karoubi C} (e : P.X ≅ Q.X)
    (h : P.p ≫ e.hom = e.hom ≫ Q.p) : P ≅ Q := by
  have hi : Q.p ≫ e.inv = e.inv ≫ P.p := by
    calc
      Q.p ≫ e.inv = e.inv ≫ (e.hom ≫ Q.p) ≫ e.inv := by simp
      _ = e.inv ≫ (P.p ≫ e.hom) ≫ e.inv := by rw [h]
      _ = e.inv ≫ P.p := by simp [Category.assoc]
  exact {
    hom := ⟨P.p ≫ e.hom, by
      simp only [← Category.assoc, P.idem]
      rw [h, Category.assoc, Q.idem]⟩
    inv := ⟨e.inv ≫ P.p, by
      calc
        Q.p ≫ (e.inv ≫ P.p) ≫ P.p = (Q.p ≫ e.inv) ≫ (P.p ≫ P.p) := by simp only [Category.assoc]
        _ = (e.inv ≫ P.p) ≫ P.p := by rw [hi, P.idem]
        _ = e.inv ≫ P.p := by rw [Category.assoc, P.idem]⟩
    hom_inv_id := by ext; simp [Category.assoc]
    inv_hom_id := by
      apply Karoubi.hom_ext
      change (e.inv ≫ P.p) ≫ (P.p ≫ e.hom) = Q.p
      rw [Category.assoc, ← Category.assoc P.p P.p e.hom, P.idem, h]
      simp }

@[simp] theorem restrictIso_hom {P Q : Karoubi C} (e : P.X ≅ Q.X)
    (h : P.p ≫ e.hom = e.hom ≫ Q.p) : (restrictIso e h).hom.f = P.p ≫ e.hom := rfl

@[simp] theorem restrictIso_inv {P Q : Karoubi C} (e : P.X ≅ Q.X)
    (h : P.p ≫ e.hom = e.hom ≫ Q.p) : (restrictIso e h).inv.f = e.inv ≫ P.p := rfl

/-- The tensor of two corners is cut out by the tensor of their idempotents. -/
def objectTensor (P Q : Karoubi C) : Karoubi C :=
  ⟨P.X ⊗ Q.X, P.p ⊗ₘ Q.p, by rw [tensorHom_comp_tensorHom, P.idem, Q.idem]⟩

def mapTensor {P P' Q Q' : Karoubi C} (f : P ⟶ P') (g : Q ⟶ Q') :
    objectTensor P Q ⟶ objectTensor P' Q' :=
  ⟨f.f ⊗ₘ g.f, by
    change (P.p ⊗ₘ Q.p) ≫ (f.f ⊗ₘ g.f) ≫ (P'.p ⊗ₘ Q'.p) = _
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, f.comm, g.comm]⟩

@[simp] theorem mapTensor_f {P P' Q Q' : Karoubi C} (f : P ⟶ P') (g : Q ⟶ Q') :
    (mapTensor f g).f = f.f ⊗ₘ g.f := rfl

/-- Naturality of the original associator makes it an isomorphism of corners. -/
def associator (P Q R : Karoubi C) :
    objectTensor (objectTensor P Q) R ≅ objectTensor P (objectTensor Q R) :=
  restrictIso (α_ P.X Q.X R.X) (associator_naturality P.p Q.p R.p)

def leftUnitor (P : Karoubi C) : objectTensor ((𝟙_ C : C) : Karoubi C) P ≅ P :=
  restrictIso (λ_ P.X) (by simpa only [objectTensor, Karoubi.coe_p, id_tensorHom] using leftUnitor_naturality P.p)

def rightUnitor (P : Karoubi C) : objectTensor P ((𝟙_ C : C) : Karoubi C) ≅ P :=
  restrictIso (ρ_ P.X) (by simpa only [objectTensor, Karoubi.coe_p, tensorHom_id] using rightUnitor_naturality P.p)

end RMod.BrundanEllis.Stacking.KaroubiTensor
