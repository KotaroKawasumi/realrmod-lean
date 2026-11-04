import RMod.Classification.Instances.LinearCategory
import RMod.Classification.Proofs.TensorCalculus
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Tensoring two even biproduct presentations

The tensor point has the pair-indexed tensor inclusions and projections.
Evenness of the first inclusions removes the interchange sign in the
matrix-unit identities. Universality is proved separately from the two
total identities, using real bilinearity of tensoring.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

variable (C : WeaklyPointedSuperfusion.{0, 0}) {I J : Type}
  {V : I → LinearCategory C} {W : J → LinearCategory C}

def tensorBicone (b : Bicone V) (c : Bicone W)
    (hbι : ∀ i, C.data.IsHomogeneous 0 (b.ι i)) :
    Bicone (C := LinearCategory C) (fun ij : I × J => C.data.tensorObj (V ij.1) (W ij.2)) where
  pt := C.data.tensorObj b.pt c.pt
  π ij := C.data.tensorHom (b.π ij.1) (c.π ij.2)
  ι ij := C.data.tensorHom (b.ι ij.1) (c.ι ij.2)
  ι_π i j := by
    classical
    change C.data.comp (C.data.tensorHom (b.ι i.1) (c.ι i.2))
      (C.data.tensorHom (b.π j.1) (c.π j.2)) = _
    rw [interchange_first_even C.laws _ _ _ _ (hbι i.1)]
    split_ifs with hij
    · subst j
      have hb : C.data.comp (b.ι i.1) (b.π i.1) = C.data.id (V i.1) := bicone_ι_π_self b i.1
      have hc : C.data.comp (c.ι i.2) (c.π i.2) = C.data.id (W i.2) := bicone_ι_π_self c i.2
      rw [hb, hc]
      exact C.laws.tensor_id _ _
    · by_cases h₁ : i.1 = j.1
      · have h₂ : i.2 ≠ j.2 := fun h => hij (Prod.ext h₁ h)
        have hc : C.data.comp (c.ι i.2) (c.π j.2) = C.data.zero := bicone_ι_π_ne c h₂
        rw [hc]
        exact tensor_zero_right C.laws _
      · have hb : C.data.comp (b.ι i.1) (b.π j.1) = C.data.zero := bicone_ι_π_ne b h₁
        rw [hb]
        exact tensor_zero_left C.laws _

end RMod.Classification
