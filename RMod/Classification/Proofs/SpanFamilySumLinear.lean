import RMod.Classification.Instances.SpanFamilyLinearCategory
import RMod.Classification.Instances.SpanFamilySumPreimage
import RMod.Classification.Proofs.SpanFamilySumPreimage

/-!
# Real linearity and exact grading of component realization

Every matrix inclusion and projection is even. Therefore the diagonal
sum preserves the common degree of a family, and extraction preserves
the degree of a map of sums. Their inverse identities show that degree
is reflected as well as preserved.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{0, 0}) {I : Type} [Fintype I] (S : I → C.data.Obj)

instance spanFamilySum_additive : (spanFamilySum C S).Additive where
  map_add {X Y} f g := by
    let p : ∀ i, @Quiver.Hom (LinearCategory C) _ (spanFamilySumObj C S X) (X i).obj :=
      fun i => (biproduct.π (spanFamilyEvenObjects C S X) i).hom
    let j : ∀ i, @Quiver.Hom (LinearCategory C) _ (Y i).obj (spanFamilySumObj C S Y) :=
      fun i => (biproduct.ι (spanFamilyEvenObjects C S Y) i).hom
    let ff : ∀ i, @Quiver.Hom (LinearCategory C) _ (X i).obj (Y i).obj := fun i => (f i).hom
    let gg : ∀ i, @Quiver.Hom (LinearCategory C) _ (X i).obj (Y i).obj := fun i => (g i).hom
    change (∑ i, (p i ≫ (ff i + gg i)) ≫ j i) =
      (∑ i, (p i ≫ ff i) ≫ j i) + ∑ i, (p i ≫ gg i) ≫ j i
    simp only [Preadditive.comp_add, Preadditive.add_comp, Finset.sum_add_distrib]

instance spanFamilySum_linear : (spanFamilySum C S).Linear ℝ where
  map_smul {X Y} f r := by
    let p : ∀ i, @Quiver.Hom (LinearCategory C) _ (spanFamilySumObj C S X) (X i).obj :=
      fun i => (biproduct.π (spanFamilyEvenObjects C S X) i).hom
    let j : ∀ i, @Quiver.Hom (LinearCategory C) _ (Y i).obj (spanFamilySumObj C S Y) :=
      fun i => (biproduct.ι (spanFamilyEvenObjects C S Y) i).hom
    let ff : ∀ i, @Quiver.Hom (LinearCategory C) _ (X i).obj (Y i).obj := fun i => (f i).hom
    change (∑ i, (p i ≫ (r • ff i)) ≫ j i) = r • ∑ i, (p i ≫ ff i) ≫ j i
    simp only [Linear.comp_smul, Linear.smul_comp, ← Finset.smul_sum]

theorem spanFamilySum_map_grade {X Y : SpanFamilyCategory C S} {a : ZMod 2}
    (f : X ⟶ Y) (hf : ∀ i, C.data.IsHomogeneous a (f i).hom) :
    C.data.IsHomogeneous a ((spanFamilySum C S).map f) := by
  change (∑ i, (show @Quiver.Hom (LinearCategory C) _ _ _ from
      C.data.comp (C.data.comp (biproduct.π (spanFamilyEvenObjects C S X) i).hom (f i).hom)
        (biproduct.ι (spanFamilyEvenObjects C S Y) i).hom)) ∈ LinearCategory.grade C _ _ a
  apply Submodule.sum_mem
  intro i _
  have h := C.laws.comp_grade _ _
    (C.laws.comp_grade _ _ (biproduct.π (spanFamilyEvenObjects C S X) i).property (hf i))
    (biproduct.ι (spanFamilyEvenObjects C S Y) i).property
  rw [zero_add, add_zero] at h
  exact h

theorem spanFamilySumPreimage_grade {X Y : SpanFamilyCategory C S} {a : ZMod 2}
    (f : (spanFamilySum C S).obj X ⟶ (spanFamilySum C S).obj Y)
    (hf : C.data.IsHomogeneous a f) (i : I) :
    C.data.IsHomogeneous a (spanFamilySumPreimage C S f i).hom := by
  have h := C.laws.comp_grade _ _
    (C.laws.comp_grade _ _ (biproduct.ι (spanFamilyEvenObjects C S X) i).property hf)
    (biproduct.π (spanFamilyEvenObjects C S Y) i).property
  rw [zero_add, add_zero] at h
  exact h

theorem spanFamilySum_map_grade_iff {X Y : SpanFamilyCategory C S} {a : ZMod 2}
    (f : X ⟶ Y) :
    C.data.IsHomogeneous a ((spanFamilySum C S).map f) ↔
      ∀ i, C.data.IsHomogeneous a (f i).hom := by
  refine ⟨fun hf i => ?_, spanFamilySum_map_grade C S f⟩
  have h := spanFamilySumPreimage_grade C S _ hf i
  rwa [spanFamilySum_preimage_map] at h

end RMod.Classification
