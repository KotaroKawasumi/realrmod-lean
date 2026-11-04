import RMod.BrundanEllis.StackingPairFactorization
import RMod.BrundanEllis.StackingKaroubiEmbeddingTensor
import RMod.BrundanEllis.StackingProductSuperMonoidal

/-! The pairing into the intrinsic completion has the composite strong
monoidal structure. Its full graded compatibility is the inclusion's
compatibility with the already constructed Koszul product tensor. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking
variable (A B : Type) [SuperCategory A] [SuperCategory B]
  [MonoidalCategory (Even A)] [MonoidalCategory (Even B)]
  [MonoidalSuperCategory A] [MonoidalSuperCategory B]

def completedPairMonoidal :
    (evenPairFunctor (KaroubiSuper.embedding (SuperTensorProduct A B))).CoreMonoidal := by
  letI := (productPairMonoidal (A := A) (B := B)).toMonoidal
  letI := (KaroubiSuper.embeddingMonoidal (SuperTensorProduct A B)).toMonoidal
  change (productPair A B ⋙ (KaroubiSuper.embedding (SuperTensorProduct A B)).forget).CoreMonoidal
  exact Functor.CoreMonoidal.ofLaxMonoidal _

theorem completedPairMonoidal_mu (X Y : Even A × Even B) :
    ((completedPairMonoidal A B).μIso X Y).hom =
      ((KaroubiSuper.embeddingMonoidal (SuperTensorProduct A B)).μIso
        ((productPair A B).obj X) ((productPair A B).obj Y)).hom := by
  change _ ≫ (KaroubiSuper.embedding (SuperTensorProduct A B)).forget.map (𝟙 _) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

theorem completedPair_tensor_natural (X X' Y Y' : Even A × Even B) :
    let F := KaroubiSuper.embedding (SuperTensorProduct A B)
    let M := completedPairMonoidal A B
    (F.map X X' ⊗ₘ F.map Y Y') ≫
      enrichedTensorMap (C := Karoubi (Even (SuperTensorProduct A B)))
        MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects _ _ _ _ ≫
      eHomWhiskerLeft SuperVec (C := Even (Karoubi (Even (SuperTensorProduct A B)))) _
        (M.μIso X' Y').hom =
    tensorμ _ _ _ _ ≫
      (enrichedTensorMap (C := A) MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects
        X.1 X'.1 Y.1 Y'.1 ⊗ₘ
       enrichedTensorMap (C := B) MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects
        X.2 X'.2 Y.2 Y'.2) ≫
      F.map (X ⊗ Y : Even A × Even B) (X' ⊗ Y' : Even A × Even B) ≫
      eHomWhiskerRight SuperVec (C := Even (Karoubi (Even (SuperTensorProduct A B))))
        (M.μIso X Y).hom _ := by
  dsimp only
  rw [completedPairMonoidal_mu, completedPairMonoidal_mu]
  have h := KaroubiSuper.embedding_tensor_natural (C := SuperTensorProduct A B)
    ((productPair A B).obj X) ((productPair A B).obj X')
    ((productPair A B).obj Y) ((productPair A B).obj Y')
  have ht : KaroubiSuper.ambientTensor
      ((productPair A B).obj X) ((productPair A B).obj X')
      ((productPair A B).obj Y) ((productPair A B).obj Y') =
      tensorμ _ _ _ _ ≫
        (enrichedTensorMap (C := A) MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects
          X.1 X'.1 Y.1 Y'.1 ⊗ₘ
         enrichedTensorMap (C := B) MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects
          X.2 X'.2 Y.2 Y'.2) := by
    change RMod.enrichedTensorMap SuperVec (productTensor A B) productTensor_objects
      ((productPair A B).obj X) ((productPair A B).obj X')
      ((productPair A B).obj Y) ((productPair A B).obj Y') = _
    rw [productTensor_aligned, productTensorMap_data]
    rfl
  rw [ht] at h
  simp only [Category.assoc] at h
  exact h

end RMod.BrundanEllis.Stacking
