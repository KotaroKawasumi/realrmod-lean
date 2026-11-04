import RMod.BrundanEllis.StackingFunctorPi
import RMod.BrundanEllis.StackingBilinear
import RMod.BrundanEllis.StackingProductSuperMonoidal
import RMod.BrundanEllis.StackingKaroubiEmbeddingMonoidal

/-! The left factor supplies the odd unit in the raw super tensor product.
The standard embedding then supplies it in the completion. Both functors
preserve the unit object definitionally, so the odd inverse laws follow
from preservation of total composition. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking
section Product
variable (A B : Type) [SuperCategory A] [SuperCategory B]
  [MonoidalCategory (Even A)] [MonoidalCategory (Even B)]
  [MonoidalSuperCategory A] [MonoidalSuperCategory B]
  [MonoidalPiSuperCategory A]

/-- Insert the right tensor unit before passing to the raw product. -/
def productPiFunctor : SuperFunctor A (SuperTensorProduct A B) :=
  insertRight SuperVec (ForgetEnrichment.to SuperVec (𝟙_ (Even B)))

instance productPi : MonoidalPiSuperCategory (SuperTensorProduct A B) where
  pi := (productPiFunctor A B).obj (MonoidalPiSuperCategory.pi (C := A))
  hom := MonoidalPiSuperCategory.hom (C := A) ≫ (productPiFunctor A B).map
    MonoidalPiSuperCategory.pi (ForgetEnrichment.to SuperVec (𝟙_ (Even A)))
  inv := MonoidalPiSuperCategory.inv (C := A) ≫ (productPiFunctor A B).map
    (ForgetEnrichment.to SuperVec (𝟙_ (Even A))) MonoidalPiSuperCategory.pi
  hom_inv := mapped_pi_hom_inv (productPiFunctor A B)
  inv_hom := mapped_pi_inv_hom (productPiFunctor A B)
end Product

namespace KaroubiSuper
variable {C : Type} [SuperCategory C] [MonoidalCategory (Even C)] [MonoidalPiSuperCategory C]

instance completedPi : MonoidalPiSuperCategory (Karoubi (Even C)) where
  pi := (embedding C).obj (MonoidalPiSuperCategory.pi (C := C))
  hom := MonoidalPiSuperCategory.hom (C := C) ≫ (embedding C).map
    MonoidalPiSuperCategory.pi (ForgetEnrichment.to SuperVec (𝟙_ (Even C)))
  inv := MonoidalPiSuperCategory.inv (C := C) ≫ (embedding C).map
    (ForgetEnrichment.to SuperVec (𝟙_ (Even C))) MonoidalPiSuperCategory.pi
  hom_inv := mapped_pi_hom_inv (embedding C)
  inv_hom := mapped_pi_inv_hom (embedding C)

end KaroubiSuper
end RMod.BrundanEllis.Stacking
