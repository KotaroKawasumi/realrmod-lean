import RMod.Enriched.FullNaturality

/-! Total-vector naturality recovers the enriched natural isomorphisms and
strong-monoidal tensor comparison used by the new equivalence interface. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe u₁ u₂
namespace RMod.EnrichedSupport
open Regression
variable {C : Type u₁} {D : Type u₂} [SuperCategory C] [SuperCategory D]

/-- Full naturality can be checked on the total graded Hom spaces. -/
def natIsoOfTotal (F G : SuperFunctor C D) (e : F.forget ≅ G.forget)
    (h : ∀ {X Y : C} (f : THom C X Y),
      tComp D (tMap F f) (evenPoint (e.hom.app (ForgetEnrichment.of SuperVec Y))) =
        tComp D (evenPoint (e.hom.app (ForgetEnrichment.of SuperVec X))) (tMap G f)) :
    EnrichedNatIso₀ SuperVec F G where
  toNatIso := e
  hom_naturality := by
    apply (degreeZero_naturality_iff SuperVec F G _).mpr
    intro X Y
    apply hom_equation_of_total
    exact fun f => h f

section
variable [MonoidalCategory (Even C)] [MonoidalCategory (Even D)]
  [MC : MonoidalEnrichedCategory SuperVec C] [MD : MonoidalEnrichedCategory SuperVec D]

/-- The tensorator is fully natural when its equation holds on total tensor points. -/
def monoidalOfTotal (F : SuperFunctor C D) (m : F.forget.CoreMonoidal)
    (h : ∀ {X X' Y Y' : Even C} (f : THom C X X') (g : THom C Y Y'),
      tComp D (tTensor (C := D) (tMap F f) (tMap F g)) (evenPoint (m.μIso X' Y').hom) =
        tComp D (evenPoint (m.μIso X Y).hom) (tMap F (tTensor (C := C) f g))) :
    MonoidalEnrichedFunctor SuperVec F where
  coreMonoidal := m
  tensorator_naturality := by
    apply (degreeZero_naturality_iff SuperVec _ _ _).mpr
    intro A B
    have hn (X X' Y Y' : Even C) :
        (F.map X X' ⊗ₘ F.map Y Y') ≫
          enrichedTensorMap SuperVec MD.tensor MD.tensor_objects (F.obj X) (F.obj X') (F.obj Y) (F.obj Y') ≫
          eHomWhiskerLeft SuperVec (ForgetEnrichment.of SuperVec (F.obj X) ⊗ ForgetEnrichment.of SuperVec (F.obj Y)) (m.μIso X' Y').hom =
        enrichedTensorMap SuperVec MC.tensor MC.tensor_objects X X' Y Y' ≫ F.map (tensorObj (C := Even C) X Y) (tensorObj (C := Even C) X' Y') ≫
          eHomWhiskerRight SuperVec (m.μIso X Y).hom (F.forget.obj (X' ⊗ Y')) := by
      let L := (F.map X X' ⊗ₘ F.map Y Y') ≫
        enrichedTensorMap SuperVec MD.tensor MD.tensor_objects (F.obj X) (F.obj X') (F.obj Y) (F.obj Y')
      let R := enrichedTensorMap SuperVec MC.tensor MC.tensor_objects X X' Y Y' ≫
        F.map (tensorObj (C := Even C) X Y) (tensorObj (C := Even C) X' Y')
      suffices L ≫ eHomWhiskerLeft SuperVec
          (ForgetEnrichment.of SuperVec (F.obj X) ⊗ ForgetEnrichment.of SuperVec (F.obj Y)) (m.μIso X' Y').hom =
          R ≫ eHomWhiskerRight SuperVec (m.μIso X Y).hom (F.forget.obj (X' ⊗ Y')) by
        simpa only [L, R, Category.assoc] using this
      apply hom_equation_of_tensor
      intro f g
      have hl : (fun a => L a (tensorPoint f g a)) = tTensor (C := D) (tMap F f) (tMap F g) := by
        funext a
        change enrichedTensorMap SuperVec MD.tensor MD.tensor_objects _ _ _ _ a
          ((F.map X X' ⊗ₘ F.map Y Y') a (tensorPoint f g a)) = _
        rw [congrFun (tensorPoint_map (F.map X X') (F.map Y Y') f g) a]
        rfl
      rw [hl]
      exact h f g
    have ht := naturality_transport_iff SuperVec
      (by simp only [enrichedTensorProductEnriched_data, EnrichedTensorProduct.of])
      (by simp only [mapThenTensor, EnrichedFunctor.comp, canonicalTensor, MonoidalCategory.tensor_obj, reobject_data,
        tensorEnrichedFunctors_data, EnrichedTensorProduct.of])
      (by simp only [mapThenTensor, EnrichedFunctor.comp, canonicalTensor, MonoidalCategory.tensor_obj, reobject_data,
        tensorEnrichedFunctors_data, EnrichedTensorProduct.of])
      (by simp only [tensorThenMap, EnrichedFunctor.comp, canonicalTensor, MonoidalCategory.tensor_obj, reobject_data,
        EnrichedTensorProduct.of])
      (by simp only [tensorThenMap, EnrichedFunctor.comp, canonicalTensor, MonoidalCategory.tensor_obj, reobject_data,
        EnrichedTensorProduct.of])
      (mapThenTensor_map_heq SuperVec F A B)
      (tensorThenMap_map_heq SuperVec F A B)
      (tensoratorApp_heq SuperVec F m A)
      (tensoratorApp_heq SuperVec F m B)
    apply ht.mpr
    simpa only [Category.assoc, ForgetEnrichment.homOf_homTo, EnrichedTensorProduct.of,
      EnrichedFunctor.forget, ForgetEnrichment.of, ForgetEnrichment.to] using hn A.1 B.1 A.2 B.2
end
end RMod.EnrichedSupport
