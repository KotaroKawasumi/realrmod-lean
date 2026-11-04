import RMod.Hierarchy.Abstract.Supercategory
import RMod.Hierarchy.Instances.SuperVecSymmetric

/-!
# Operations of the enriched tensor product

Objects are pairs. Composition interchanges the middle Hom objects using
the Koszul braiding before composing in the two factors.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.Legacy

def superTensorProductData (C D : SupercategoryData) : SupercategoryData where
  Obj := C.Obj × D.Obj
  Hom X Y := C.Hom X.1 Y.1 ⊗ D.Hom X.2 Y.2
  id X := (λ_ (𝟙_ SuperVec)).inv ≫ (C.id X.1 ⊗ₘ D.id X.2)
  comp X Y Z := tensorμ _ _ _ _ ≫ (C.comp X.1 Y.1 Z.1 ⊗ₘ D.comp X.2 Y.2 Z.2)

end RMod.Legacy
