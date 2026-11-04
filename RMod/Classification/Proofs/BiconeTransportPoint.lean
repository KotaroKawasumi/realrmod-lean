import RMod.Classification.Instances.BiconeTransportPoint

/-! # Universality of the explicitly transported presentation -/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

variable {C : Type*} [Category C] [Preadditive C] {I : Type*} [Fintype I] {V : I → C}

noncomputable def biconeTransportPoint_isBilimit (b : Bicone V) (hb : b.IsBilimit)
    {X : C} (e : b.pt ≅ X) : (biconeTransportPoint b e).IsBilimit := by
  apply isBilimitOfTotal
  change (∑ i, (e.inv ≫ b.π i) ≫ (b.ι i ≫ e.hom)) = 𝟙 X
  calc
    _ = e.inv ≫ (∑ i, b.π i ≫ b.ι i) ≫ e.hom := by
      simp only [comp_sum, sum_comp, Category.assoc]
    _ = 𝟙 X := by rw [IsBilimit.total hb, Category.id_comp, e.inv_hom_id]

end RMod.Classification
