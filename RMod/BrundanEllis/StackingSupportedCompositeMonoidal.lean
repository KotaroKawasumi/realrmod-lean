import RMod.BrundanEllis.StackingSemigroupalComposite
import RMod.BrundanEllis.StackingRelativeTensorComposition

/-! Strong monoidality of an enriched composite whose second comparison
is invertible on the first functor's image. Unit data come from the
ordinary equivalence already established for that same composite. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable {C D E : Type} [SuperCategory C] [SuperCategory D] [SuperCategory E]
  [MonoidalCategory (Even C)] [MonoidalCategory (Even D)] [MonoidalCategory (Even E)]
  [MonoidalSuperCategory C] [MonoidalSuperCategory D] [MonoidalSuperCategory E]
  (F : SuperFunctor C D) (G : SuperFunctor D E)
  (M : F.forget.CoreMonoidal)
  (ν : ∀ X Y : Even D, G.forget.obj X ⊗ G.forget.obj Y ⟶ G.forget.obj (X ⊗ Y))
  (hnL : ∀ {X Y : Even D} (u : X ⟶ Y) (Z : Even D),
    G.forget.map u ▷ G.forget.obj Z ≫ ν Y Z = ν X Z ≫ G.forget.map (u ▷ Z))
  (hnR : ∀ {X Y : Even D} (Z : Even D) (u : X ⟶ Y),
    G.forget.obj Z ◁ G.forget.map u ≫ ν Z Y = ν Z X ≫ G.forget.map (Z ◁ u))
  (ha : ∀ X Y Z : Even D,
    ν X Y ▷ G.forget.obj Z ≫ ν (X ⊗ Y) Z ≫ G.forget.map (α_ X Y Z).hom =
      (α_ (G.forget.obj X) (G.forget.obj Y) (G.forget.obj Z)).hom ≫
        G.forget.obj X ◁ ν Y Z ≫ ν X (Y ⊗ Z))
  (N : ∀ X Y : Even C, G.forget.obj (F.forget.obj X) ⊗ G.forget.obj (F.forget.obj Y) ≅
    G.forget.obj (F.forget.obj X ⊗ F.forget.obj Y))
  (hN : ∀ X Y, (N X Y).hom = ν (F.forget.obj X) (F.forget.obj Y))
  [(F.comp SuperVec G).forget.IsEquivalence]

include hnL hnR ha hN in
/-- Normalize the unit and transfer the ordinary composite structure through forgetComp. -/
def supportedCompositeCoreMonoidal : (F.comp SuperVec G).forget.CoreMonoidal := by
  letI := Functor.isEquivalence_of_iso (EnrichedFunctor.forgetComp F G)
  let P := coreMonoidalOfSupportedComposite F.forget G.forget M ν hnL hnR ha N hN
  letI := P.toMonoidal
  letI := Functor.Monoidal.transport (EnrichedFunctor.forgetComp F G).symm
  exact Functor.CoreMonoidal.ofLaxMonoidal _

/-- The transferred tensorator still consists of exactly the two chosen binary maps. -/
theorem supportedCompositeCoreMonoidal_tensor (X Y : Even C) :
    ((supportedCompositeCoreMonoidal F G M ν hnL hnR ha N hN).μIso X Y).hom =
      ν (F.forget.obj X) (F.forget.obj Y) ≫ G.forget.map (M.μIso X Y).hom := by
  change (𝟙 _ ⊗ₘ 𝟙 _) ≫ ((N X Y).hom ≫ G.forget.map (M.μIso X Y).hom) ≫ 𝟙 _ = _
  rw [id_tensorHom_id, Category.id_comp, Category.comp_id, hN]

/-- The supported composite is monoidal on the entire enriched Hom, not only even maps. -/
theorem supportedCompositeCoreMonoidal_enriched
    (hM : ∀ X X' Y Y' : Even C,
      (F.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec X') ⊗ₘ
        F.map (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Y')) ≫
        KaroubiSuper.ambientTensor (F.forget.obj X) (F.forget.obj X') (F.forget.obj Y) (F.forget.obj Y') ≫
        eHomWhiskerLeft SuperVec (F.forget.obj X ⊗ F.forget.obj Y) (M.μIso X' Y').hom =
      KaroubiSuper.ambientTensor X X' Y Y' ≫
        F.map (ForgetEnrichment.to SuperVec (X ⊗ Y)) (ForgetEnrichment.to SuperVec (X' ⊗ Y')) ≫
        eHomWhiskerRight SuperVec (M.μIso X Y).hom (F.forget.obj (X' ⊗ Y')))
    (hν : ∀ X X' Y Y' : Even D,
      (G.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec X') ⊗ₘ
        G.map (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Y')) ≫
        KaroubiSuper.ambientTensor (G.forget.obj X) (G.forget.obj X') (G.forget.obj Y) (G.forget.obj Y') ≫
        eHomWhiskerLeft SuperVec (G.forget.obj X ⊗ G.forget.obj Y) (ν X' Y') =
      KaroubiSuper.ambientTensor X X' Y Y' ≫
        G.map (ForgetEnrichment.to SuperVec (X ⊗ Y)) (ForgetEnrichment.to SuperVec (X' ⊗ Y')) ≫
        eHomWhiskerRight SuperVec (ν X Y) (G.forget.obj (X' ⊗ Y')))
    (X X' Y Y' : Even C) :
    let H := F.comp SuperVec G
    let P := supportedCompositeCoreMonoidal F G M ν hnL hnR ha N hN
    (H.map (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec X') ⊗ₘ
      H.map (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Y')) ≫
      KaroubiSuper.ambientTensor (H.forget.obj X) (H.forget.obj X') (H.forget.obj Y) (H.forget.obj Y') ≫
      eHomWhiskerLeft SuperVec (H.forget.obj X ⊗ H.forget.obj Y) (P.μIso X' Y').hom =
    KaroubiSuper.ambientTensor X X' Y Y' ≫
      H.map (ForgetEnrichment.to SuperVec (X ⊗ Y)) (ForgetEnrichment.to SuperVec (X' ⊗ Y')) ≫
      eHomWhiskerRight SuperVec (P.μIso X Y).hom (H.forget.obj (X' ⊗ Y')) := by
  dsimp only
  rw [supportedCompositeCoreMonoidal_tensor, supportedCompositeCoreMonoidal_tensor]
  exact composite_relative_tensor_natural F G M ν hM hν X X' Y Y'

end RMod.BrundanEllis.Stacking
