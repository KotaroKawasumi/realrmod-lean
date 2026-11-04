import RMod.BrundanEllis.StackingHullCategory
import RMod.Enriched.SplitImages
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Preadditive.Schur

/-! The diagonal completion is an abelian full subcategory. In the ambient
finite semisimple category every mono and epi splits, so closure under retracts
implies closure under kernels and cokernels. No new semisimplicity hypothesis
is added to the completion. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open scoped ZeroObject
namespace RMod.BrundanEllis

variable {C : WeaklyPointedFusionPiSuperCat} {I : Type} {Z : I → Even C}

namespace Stacking
/-- Schur's lemma and the given finite simple decompositions split every image. -/
theorem ambient_split_image {X Y : Even C} (f : X ⟶ Y) :
    RMod.EnrichedSupport.HasSplitImage f := by
  apply RMod.EnrichedSupport.split_images_of_semisimple
    (FusionPiSuperCategory.semisimple (C := C))
  intro S T hS hT g hg
  letI := hS
  letI := hT
  exact isIso_of_hom_simple hg

/-- In a finite semisimple category every subobject is an actual even retract. -/
theorem mono_retract {X Y : Even C} (f : X ⟶ Y) [Mono f] : Nonempty (Retract X Y) := by
  obtain ⟨J, p, i, s, r, hp, hi, hf⟩ := ambient_split_image f
  have hps : p ≫ s = 𝟙 X := by
    apply (cancel_mono f).mp
    rw [← hf]
    simp only [Category.id_comp, Category.assoc, ← Category.assoc s p i, hp]
  refine ⟨{ i := f, r := r ≫ s, retract := ?_ }⟩
  rw [← hf]
  rw [Category.assoc, ← Category.assoc i r s, hi, Category.id_comp, hps]

/-- Every quotient in the ambient category is likewise an even retract. -/
theorem epi_retract {X Y : Even C} (f : X ⟶ Y) [Epi f] : Nonempty (Retract Y X) := by
  obtain ⟨J, p, i, s, r, hp, hi, hf⟩ := ambient_split_image f
  have hri : r ≫ i = 𝟙 Y := by
    apply (cancel_epi f).mp
    rw [← hf]
    simp [Category.assoc, ← Category.assoc i r i, hi]
  refine ⟨{ i := r ≫ s, r := f, retract := ?_ }⟩
  rw [← hf]
  simpa [Category.assoc, ← Category.assoc s p i, hp] using hri
end Stacking

namespace AddPiHull
instance closedSubobjects : ObjectProperty.IsClosedUnderSubobjects (AddPiHull C Z) where
  prop_of_mono f _ h := of_retract (Stacking.mono_retract f).some h

instance closedQuotients : ObjectProperty.IsClosedUnderQuotients (AddPiHull C Z) where
  prop_of_epi f _ h := of_retract (Stacking.epi_retract f).some h

instance containsZero : ObjectProperty.ContainsZero (AddPiHull C Z) where
  exists_zero := ⟨0, isZero_zero _, 0, Fin.elim0, Fin.elim0,
    ⟨{ i := 0, r := 0, retract := by simp }⟩⟩

instance closedFiniteProducts :
    ObjectProperty.IsClosedUnderFiniteProducts (AddPiHull C Z) where
  isClosedUnderLimitsOfShape J _ := by
    classical
    letI : Fintype J := Fintype.ofFinite J
    apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
    rintro _ ⟨F, hF⟩
    let X : J → Even C := fun j => F.obj ⟨j⟩
    have hs : AddPiHull C Z (⨁ X) := finite_biproduct X (fun j => hF ⟨j⟩)
    let e : F ≅ Discrete.functor X := Discrete.natIso (fun _ => Iso.refl _)
    exact (iso_iff ((HasLimit.isoOfNatIso e) ≪≫ (biproduct.isoProduct X).symm)).mpr hs

end AddPiHull

/-- Abelianity follows from the proved closure properties of the actual hull. -/
instance hullAbelian : Abelian (ObjectProperty.FullSubcategory (AddPiHull C Z)) :=
  inferInstance

end RMod.BrundanEllis
