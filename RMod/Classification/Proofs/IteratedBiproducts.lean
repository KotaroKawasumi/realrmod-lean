import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Inclusions in an iterated biproduct

The canonical comparison with the biproduct over pairs carries a nested
inclusion to the inclusion of that pair. This is an equality of actual
maps, obtained by testing against all canonical projections.
-/

set_option autoImplicit false
universe u v w z

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]
  {I : Type w} {J : Type z} (F : I → J → V)
  [∀ i, HasBiproduct (F i)] [HasBiproduct (fun i => ⨁ (F i))]

theorem iteratedBiproduct_inclusion (i : I) (j : J) :
    biproduct.ι (F i) j ≫ biproduct.ι (fun i => ⨁ (F i)) i ≫
      (biproductBiproductIso (fun _ : I => J) F).hom =
        biproduct.ι (fun x : (_ : I) × J => F x.1 x.2) ⟨i, j⟩ := by
  classical
  apply biproduct.hom_ext
  intro ⟨a, b⟩
  by_cases ha : i = a
  · subst a
    by_cases hb : j = b
    · subst b
      simp [biproductBiproductIso_hom, Category.assoc]
    · have hp : (⟨i, j⟩ : (_ : I) × J) ≠ ⟨i, b⟩ := fun he => hb (congrArg Sigma.snd he)
      simp [biproductBiproductIso_hom, Category.assoc, biproduct.ι_π_ne _ hb,
        biproduct.ι_π_ne _ hp]
  · have hp : (⟨i, j⟩ : (_ : I) × J) ≠ ⟨a, b⟩ := fun he => ha (congrArg Sigma.fst he)
    simp [biproductBiproductIso_hom, Category.assoc, biproduct.ι_π_ne_assoc _ ha,
      biproduct.ι_π_ne _ hp]

end RMod.Classification
