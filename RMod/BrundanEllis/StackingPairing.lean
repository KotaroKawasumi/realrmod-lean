import RMod.BrundanEllis.Classification

/-! The ordinary exterior pairing induced by the super tensor-product enrichment. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis

@[reassoc] private theorem unit_interchange :
    (λ_ (𝟙_ SuperVec)).inv ≫ ((λ_ (𝟙_ SuperVec)).inv ⊗ₘ (λ_ (𝟙_ SuperVec)).inv) ≫
      tensorμ (𝟙_ SuperVec) (𝟙_ SuperVec) (𝟙_ SuperVec) (𝟙_ SuperVec) =
    (λ_ (𝟙_ SuperVec)).inv ≫ ((λ_ (𝟙_ SuperVec)).inv ⊗ₘ (λ_ (𝟙_ SuperVec)).inv) := by
  simp only [tensorμ, braiding_tensorUnit_left]
  monoidal

/-- The object map fixes Hom types; the morphism formula is specified by evenPair_data. -/
def evenPair {A B D : WeaklyPointedFusionPiSuperCat}
    (F : SuperFunctor (SuperTensorProduct A B) D) : Even A × Even B ⥤ Even D where
  obj X := evenObj D (F.obj (ForgetEnrichment.to SuperVec X.1, ForgetEnrichment.to SuperVec X.2))
  map {X Y} f := ForgetEnrichment.homOf SuperVec
    ((λ_ (𝟙_ SuperVec)).inv ≫
      (ForgetEnrichment.homTo SuperVec f.1 ⊗ₘ ForgetEnrichment.homTo SuperVec f.2) ≫
      F.map (ForgetEnrichment.to SuperVec X.1, ForgetEnrichment.to SuperVec X.2) (ForgetEnrichment.to SuperVec Y.1, ForgetEnrichment.to SuperVec Y.2))
  map_id X := by
    apply_fun ForgetEnrichment.homTo SuperVec
    · simp only [ForgetEnrichment.homTo_homOf, ForgetEnrichment.homTo_id,
        CategoryTheory.prod_id_fst, CategoryTheory.prod_id_snd]
      change eId SuperVec (C := SuperTensorProduct A B) (ForgetEnrichment.to SuperVec X.1, ForgetEnrichment.to SuperVec X.2) ≫ F.map (ForgetEnrichment.to SuperVec X.1, ForgetEnrichment.to SuperVec X.2) (ForgetEnrichment.to SuperVec X.1, ForgetEnrichment.to SuperVec X.2) = _
      exact F.map_id _
    · intro f g h
      exact congrArg (ForgetEnrichment.homOf SuperVec) h
  map_comp {X Y Z} f g := by
    apply_fun ForgetEnrichment.homTo SuperVec
    · simp only [ForgetEnrichment.homTo_homOf, ForgetEnrichment.homTo_comp,
        CategoryTheory.prod_comp_fst, CategoryTheory.prod_comp_snd, Category.assoc]
      simp only [evenObj, ForgetEnrichment.to_of, ← tensorHom_comp_tensorHom_assoc]
      rw [← F.map_comp (ForgetEnrichment.to SuperVec X.1, ForgetEnrichment.to SuperVec X.2) (ForgetEnrichment.to SuperVec Y.1, ForgetEnrichment.to SuperVec Y.2) (ForgetEnrichment.to SuperVec Z.1, ForgetEnrichment.to SuperVec Z.2)]
      change _ = (λ_ (𝟙_ SuperVec)).inv ≫
        ((λ_ (𝟙_ SuperVec)).inv ⊗ₘ (λ_ (𝟙_ SuperVec)).inv) ≫
        ((ForgetEnrichment.homTo SuperVec f.1 ⊗ₘ ForgetEnrichment.homTo SuperVec f.2) ⊗ₘ
          (ForgetEnrichment.homTo SuperVec g.1 ⊗ₘ ForgetEnrichment.homTo SuperVec g.2)) ≫
        tensorμ _ _ _ _ ≫
        (eComp SuperVec (ForgetEnrichment.to SuperVec X.1) (ForgetEnrichment.to SuperVec Y.1) (ForgetEnrichment.to SuperVec Z.1) ⊗ₘ eComp SuperVec (ForgetEnrichment.to SuperVec X.2) (ForgetEnrichment.to SuperVec Y.2) (ForgetEnrichment.to SuperVec Z.2)) ≫ F.map _ _
      rw [tensorμ_natural_assoc]
      rw [unit_interchange_assoc]
      rfl
    · intro f g h
      exact congrArg (ForgetEnrichment.homOf SuperVec) h

theorem evenPair_data {A B D : WeaklyPointedFusionPiSuperCat}
    (F : SuperFunctor (SuperTensorProduct A B) D) :
    (∀ X, (evenPair F).obj X = evenObj D (F.obj (X.1, X.2))) ∧
    (∀ X Y (f : X ⟶ Y), ForgetEnrichment.homTo SuperVec ((evenPair F).map f) =
      (λ_ (𝟙_ SuperVec)).inv ≫
        (ForgetEnrichment.homTo SuperVec f.1 ⊗ₘ ForgetEnrichment.homTo SuperVec f.2) ≫
        F.map (X.1, X.2) (Y.1, Y.2)) := ⟨fun _ => rfl, fun _ _ _ => rfl⟩

end RMod.BrundanEllis
