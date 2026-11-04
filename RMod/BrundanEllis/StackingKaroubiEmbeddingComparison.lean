import RMod.BrundanEllis.StackingKaroubiEmbeddingMonoidal

/-! The embedding's tensor comparison is the identity on the underlying
ambient object. This computation will reflect its full graded tensor
compatibility through the faithful corner inclusions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable {C : Type} [SuperCategory C] [MonoidalCategory (Even C)]

instance comparisonIsMonoidal : (evenEquivalence (C := C)).IsMonoidal := by
  change (Monoidal.equivalenceTransported (evenEquivalence (C := C)).symm).symm.IsMonoidal
  infer_instance

theorem inverseComparison_mu_map (P Q : Karoubi (Even C)) :
    (evenEquivalence (C := C)).functor.map
      (Functor.LaxMonoidal.μ (evenEquivalence (C := C)).inverse P Q) = 𝟙 (P ⊗ Q) := by
  have h := (evenEquivalence (C := C)).functor_map_μ_inverse_comp_counit_app_tensor P Q
  change (evenEquivalence (C := C)).functor.map
      (Functor.LaxMonoidal.μ (evenEquivalence (C := C)).inverse P Q) ≫ 𝟙 (P ⊗ Q) =
    𝟙 (P ⊗ Q) ≫ (𝟙 P ⊗ₘ 𝟙 Q) at h
  exact (Category.comp_id _).symm.trans (h.trans (by simp only [Category.id_comp, id_tensorHom_id]))

theorem embeddingMonoidal_mu_map (X Y : Even C) :
    ((evenEquivalence (C := C)).functor.map ((embeddingMonoidal C).μIso X Y).hom).f =
      𝟙 (X ⊗ Y) := by
  change ((evenEquivalence (C := C)).functor.map
    (Functor.LaxMonoidal.μ (evenEquivalence (C := C)).inverse
      ((X : Even C) : Karoubi (Even C)) ((Y : Even C) : Karoubi (Even C)) ≫
      (evenEquivalence (C := C)).inverse.map ((KaroubiTensor.inclusionMonoidal (Even C)).μIso X Y).hom)).f = _
  rw [Functor.map_comp, even_map_inverse, inverseComparison_mu_map]
  change (𝟙 (((X : Even C) : Karoubi (Even C)) ⊗ ((Y : Even C) : Karoubi (Even C))) ≫
    ((KaroubiTensor.inclusionMonoidal (Even C)).μIso X Y).hom).f = _
  rw [Category.id_comp]
  simp only [KaroubiTensor.inclusionMonoidal, KaroubiTensor.restrictIso_hom,
    KaroubiTensor.objectTensor, KaroubiTensor.tensorObj_p, Karoubi.coe_p, Iso.refl_hom,
    id_tensorHom_id, Category.comp_id]
  exact Category.id_comp _

end RMod.BrundanEllis.Stacking.KaroubiSuper
