import RMod.Classification.Instances.LinearMonoidal
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# A full-Hom bicone whose structural maps are even

Retain the point and every structural map while recording their proved
evenness in the existing even-category adapter. The real-field adapter
is noncomputable; the underlying maps are exactly the supplied maps.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits Superfusion.Category

noncomputable def biconeToEven (C : WeaklyPointedSuperfusion.{0, 0})
    {I : Type} {V : I → LinearCategory C} (b : Bicone V)
    (hπ : ∀ i, C.data.IsHomogeneous 0 (b.π i)) (hι : ∀ i, C.data.IsHomogeneous 0 (b.ι i)) :
    Bicone (fun i => evenObj ℝ (LinearCategory C) (V i)) where
  pt := evenObj ℝ (LinearCategory C) b.pt
  π i := ⟨b.π i, hπ i⟩
  ι i := ⟨b.ι i, hι i⟩
  ι_π i j := by
    classical
    split_ifs with h
    · subst j
      apply WideSubcategory.hom_ext
      exact bicone_ι_π_self b i
    · apply WideSubcategory.hom_ext
      exact bicone_ι_π_ne b h

end RMod.Classification
