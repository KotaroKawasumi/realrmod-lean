import RMod.Classification.Instances.LinearCategory

/-!
# Inverting and comparing scalar intertwining equations

An involutive scalar sign is unchanged when an intertwiner is inverted.
The ratio of two invertible intertwiners consequently commutes with the
target action up to the product of their two signs.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {C : Type*} [Category C] [Preadditive C] [Linear ℝ C]
  {X Y : C} {r s : ℝ} (e : X ≅ Y) (f : X ⟶ X) (g : Y ⟶ Y)

theorem signed_intertwining_inverse (hr : r * r = 1)
    (h : f ≫ e.hom = r • (e.hom ≫ g)) :
    g ≫ e.inv = r • (e.inv ≫ f) := by
  have he := congrArg (fun k => e.inv ≫ k ≫ e.inv) h
  simp only [Linear.comp_smul, Linear.smul_comp, Category.assoc, Iso.hom_inv_id,
    Iso.inv_hom_id_assoc, Category.comp_id] at he
  calc
    _ = r • (r • (g ≫ e.inv)) := by rw [smul_smul, hr, one_smul]
    _ = _ := congrArg (fun k => r • k) he.symm

theorem signed_intertwining_ratio (t : X ≅ Y) (hr : r * r = 1)
    (he : f ≫ e.hom = r • (e.hom ≫ g)) (ht : f ≫ t.hom = s • (t.hom ≫ g)) :
    g ≫ (e.inv ≫ t.hom) = (r * s) • ((e.inv ≫ t.hom) ≫ g) := by
  rw [← Category.assoc, signed_intertwining_inverse e f g hr he,
    Linear.smul_comp, Category.assoc, ht, Linear.comp_smul, smul_smul, Category.assoc]

end RMod.Classification
