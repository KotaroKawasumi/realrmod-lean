import RMod.BrundanEllis.StackingKaroubiFunctorMonoidal
import RMod.BrundanEllis.StackingKaroubiEmbeddingComparison

/-! Compute the tensor comparison of the enriched corner functor in the
ambient category. This is the formula needed to check all homogeneous
arrows against the original functor's tensor comparison. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable {C D : Type} [SuperCategory C] [SuperCategory D]
  [MonoidalCategory (Even C)] [MonoidalCategory (Even D)]

theorem forwardComparison_mu (P Q : Even (Karoubi (Even C))) :
    Functor.LaxMonoidal.μ (evenEquivalence (C := C)).functor P Q =
      𝟙 ((ForgetEnrichment.to SuperVec P) ⊗ (ForgetEnrichment.to SuperVec Q)) := by
  rfl

theorem functorMonoidal_mu_map (F : SuperFunctor C D) (M : F.forget.CoreMonoidal)
    (P Q : Even (Karoubi (Even C))) :
    ((evenEquivalence (C := D)).functor.map ((functorMonoidal F M).μIso P Q).hom).f =
      (F.forget.map (ForgetEnrichment.to SuperVec P).p ⊗ₘ
        F.forget.map (ForgetEnrichment.to SuperVec Q).p) ≫
        (M.μIso (ForgetEnrichment.to SuperVec P).X (ForgetEnrichment.to SuperVec Q).X).hom := by
  letI := M.toMonoidal
  change ((evenEquivalence (C := D)).functor.map
    ((Functor.LaxMonoidal.μ (evenEquivalence (C := D)).inverse _ _ ≫
      (evenEquivalence (C := D)).inverse.map
        ((KaroubiTensor.mapMonoidal F.forget).μIso _ _).hom) ≫
      (evenEquivalence (C := D)).inverse.map ((KaroubiTensor.mapFunctor F.forget).map
        (Functor.LaxMonoidal.μ (evenEquivalence (C := C)).functor P Q)))).f = _
  rw [Functor.map_comp, Functor.map_comp, even_map_inverse, even_map_inverse,
    inverseComparison_mu_map, forwardComparison_mu]
  change ((𝟙 ((KaroubiTensor.mapFunctor F.forget).obj (ForgetEnrichment.to SuperVec P) ⊗
      (KaroubiTensor.mapFunctor F.forget).obj (ForgetEnrichment.to SuperVec Q)) ≫
      ((KaroubiTensor.mapMonoidal F.forget).μIso (ForgetEnrichment.to SuperVec P)
        (ForgetEnrichment.to SuperVec Q)).hom) ≫
      (KaroubiTensor.mapFunctor F.forget).map
        (𝟙 (ForgetEnrichment.to SuperVec P ⊗ ForgetEnrichment.to SuperVec Q))).f = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  simp only [Category.id_comp, Category.comp_id, KaroubiTensor.mapMonoidal,
    KaroubiTensor.mapTensorIso, KaroubiTensor.restrictIso_hom,
    KaroubiTensor.tensorObj_p, KaroubiTensor.mapFunctor]
  rfl

/-- The comparison is the actual restriction of the original tensorator. -/
theorem functorMonoidal_mu_cut (F : SuperFunctor C D) (M : F.forget.CoreMonoidal)
    (P Q : Even (Karoubi (Even C))) :
    (evenEquivalence (C := D)).functor.map ((functorMonoidal F M).μIso P Q).hom =
      KaroubiTensor.cut
        (P := KaroubiTensor.objectTensor (mapObject F (ForgetEnrichment.to SuperVec P))
          (mapObject F (ForgetEnrichment.to SuperVec Q)))
        (Q := mapObject F (KaroubiTensor.objectTensor (ForgetEnrichment.to SuperVec P)
          (ForgetEnrichment.to SuperVec Q)))
        (M.μIso (ForgetEnrichment.to SuperVec P).X (ForgetEnrichment.to SuperVec Q).X).hom (by
          letI := M.toMonoidal
          change (F.forget.map (ForgetEnrichment.to SuperVec P).p ⊗ₘ
            F.forget.map (ForgetEnrichment.to SuperVec Q).p) ≫ _ = _ ≫
            F.forget.map ((ForgetEnrichment.to SuperVec P).p ⊗ₘ (ForgetEnrichment.to SuperVec Q).p)
          exact Functor.LaxMonoidal.μ_natural F.forget _ _) := by
  apply Karoubi.hom_ext
  exact functorMonoidal_mu_map F M P Q

end RMod.BrundanEllis.Stacking.KaroubiSuper
