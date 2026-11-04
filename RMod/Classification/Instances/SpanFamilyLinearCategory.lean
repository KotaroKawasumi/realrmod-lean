import RMod.Classification.Abstract.SpanFamily
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Pointwise real-linear structure on component families

The Hom spaces in Mathlib's product category are dependent products.
Their existing additive-group and module instances give the pointwise
linear structure, without changing any of the category operations.
-/

set_option autoImplicit false

namespace RMod.Classification.SpanFamilyCategory

open CategoryTheory

variable (C : WeaklyPointedSuperfusion.{0, 0}) {I : Type} (S : I → C.data.Obj)

instance preadditive : Preadditive (SpanFamilyCategory C S) where
  homGroup X Y := inferInstanceAs (AddCommGroup ((i : I) → (X i ⟶ Y i)))
  add_comp _ _ _ f g h := funext fun i => Preadditive.add_comp _ _ _ (f i) (g i) (h i)
  comp_add _ _ _ f g h := funext fun i => Preadditive.comp_add _ _ _ (f i) (g i) (h i)

instance linear : Linear ℝ (SpanFamilyCategory C S) where
  homModule X Y := inferInstanceAs (Module ℝ ((i : I) → (X i ⟶ Y i)))
  smul_comp _ _ _ r f g := funext fun i => Linear.smul_comp _ _ _ r (f i) (g i)
  comp_smul _ _ _ f r g := funext fun i => Linear.comp_smul _ _ _ (f i) r (g i)

end RMod.Classification.SpanFamilyCategory
