import RMod.BrundanEllis.StackingHullAbelian
import Mathlib.CategoryTheory.Abelian.Transfer

/-! Finite semisimplicity passes to the completion because each simple summand
is an even retract. The enrichment and the ordinary full subcategory use the
same Hom spaces; their canonical equivalence transfers the abelian structure. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis
variable (C : WeaklyPointedFusionPiSuperCat) {I : Type} (Z : I → Even C)

/-- Forgetting this inherited enrichment recovers the ordinary full subcategory. -/
def hullEvenEquivalence : Even (HullCategory C Z) ≌
    ObjectProperty.FullSubcategory (AddPiHull C Z) := by
  with_unfolding_all
    exact ForgetEnrichment.equiv SuperVec (D := ObjectProperty.FullSubcategory (AddPiHull C Z))

instance hullEvenAbelian : Abelian (Even (HullCategory C Z)) := by
  let F := (hullEvenEquivalence C Z).functor
  letI : HasFiniteProducts (Even (HullCategory C Z)) :=
    ⟨fun _ => Adjunction.hasLimitsOfShape_of_equivalence F⟩
  exact abelianOfEquivalence F

/-- The underlying inclusion factors through the canonical ordinary equivalence. -/
theorem hullInclusion_evenFactor : (hullInclusion C Z).forget =
    (hullEvenEquivalence C Z).functor ⋙ ObjectProperty.ι (AddPiHull C Z) := by
  apply CategoryTheory.Functor.ext
  · intro X Y f
    simp [hullInclusion, hullEvenEquivalence, EnrichedFunctor.forget,
      ForgetEnrichment.equiv, ForgetEnrichment.equivFunctor,
      ObjectProperty.ι, eHomEquiv]
    rfl
  · intro X; rfl

instance hullInclusionFull : (hullInclusion C Z).forget.Full := by
  rw [hullInclusion_evenFactor]
  infer_instance
instance hullInclusionFaithful : (hullInclusion C Z).forget.Faithful := by
  rw [hullInclusion_evenFactor]
  infer_instance
instance hullInclusionAdditive : (hullInclusion C Z).forget.Additive := by
  exact { map_add := by intros; rfl }

instance hullInclusionMono : (hullInclusion C Z).forget.PreservesMonomorphisms := by
  rw [hullInclusion_evenFactor]
  letI : IsNormalEpiCategory (Even C) := by
    have hz := Subsingleton.elim
      (@Preadditive.preadditiveHasZeroMorphisms (Even C) _ C.abelian.toPreadditive)
      (@Preadditive.preadditiveHasZeroMorphisms (Even C) _ (evenCategoryPreadditive C))
    exact hz ▸ C.abelian.toIsNormalEpiCategory
  letI := ObjectProperty.preservesMonomorphisms_ι_of_isNormalEpiCategory (AddPiHull C Z)
  infer_instance

/-- Ambient simple objects remain simple in the full subcategory. -/
theorem hull_simple_of_ambient (X : Even (HullCategory C Z))
    (h : Simple ((hullInclusion C Z).forget.obj X)) : Simple X := by
  let F := (hullInclusion C Z).forget
  letI := h
  refine ⟨fun f _ => ?_⟩
  exact (isIso_iff_of_reflects_iso f F).symm.trans
    ((Simple.mono_isIso_iff_nonzero (F.map f)).trans (not_congr (Functor.map_eq_zero_iff F)))

/-- Each ambient simple summand belongs to the same hull as the original object. -/
theorem hull_semisimple (X : Even (HullCategory C Z)) :
    ∃ (n : ℕ) (S : Fin n → Even (HullCategory C Z)),
      (∀ i, Simple (S i)) ∧ Nonempty (X ≅ ⨁ S) := by
  obtain ⟨n, S, hS, ⟨e⟩⟩ := FusionPiSuperCategory.semisimple (C := C) X.obj
  have hmem (i : Fin n) : AddPiHull C Z (S i) := by
    apply AddPiHull.of_retract (Y := X.obj) _ X.property
    exact {
      i := biproduct.ι S i ≫ e.inv
      r := e.hom ≫ biproduct.π S i
      retract := by simp [Category.assoc] }
  let T : Fin n → Even (HullCategory C Z) := fun i => evenObj _ ⟨S i, hmem i⟩
  let F := (hullInclusion C Z).forget
  refine ⟨n, T, fun i => hull_simple_of_ambient C Z (T i) (hS i), ?_⟩
  exact ⟨F.preimageIso (e ≪≫ (F.mapBiproduct T).symm)⟩

end RMod.BrundanEllis
