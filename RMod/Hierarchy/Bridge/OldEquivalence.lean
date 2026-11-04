import RMod.Hierarchy.Bridge.OldEvenValues
import RMod.Hierarchy.Bridge.OldEquivalenceNaturality

/-!
# Monoidal superequivalences survive enrichment

The even comparison maps retain their values and all coherence equations.
Together with total naturality, this transports the actual equivalence
witness produced by the existing classification proofs.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.Legacy.Hierarchy
variable {C D : WeaklyPointedSuperfusion.{0, 0}} (E : Classification.MonoidalSuperequivalence C D)

theorem ofOldMonoidalSuperequivalenceLaws : MonoidalSuperequivalenceLaws (ofOldMonoidalSuperequivalenceData E) where
  forward := ofOldSuperfunctorLaws (ofOldEquivalenceForward E)
  backward := ofOldSuperfunctorLaws (ofOldEquivalenceBackward E)
  unit_natural := ofOldEquivalence_unit_natural E
  counit_natural := ofOldEquivalence_counit_natural E
  tensor_natural := ofOldEquivalence_tensor_natural E
  associativity X Y Z := by
    let F := Superfunctor.enriched (ofOldSuperfunctor (ofOldEquivalenceForward E))
    let d := ofOldMonoidalSuperequivalenceData E
    let FX : Even (ofOldSupercategory D) := evenObj _ (E.data.forward.obj X)
    let FY : Even (ofOldSupercategory D) := evenObj _ (E.data.forward.obj Y)
    let FZ : Even (ofOldSupercategory D) := evenObj _ (E.data.forward.obj Z)
    let μ₁ := (d.tensorIso X Y).hom
    let μ₂ := (d.tensorIso (X ⊗ Y) Z).hom
    let μ₃ := (d.tensorIso Y Z).hom
    let μ₄ := (d.tensorIso X (Y ⊗ Z)).hom
    let a := F.forget.map (α_ X Y Z).hom
    apply (evenHomEquiv D _ _).injective
    apply WideSubcategory.hom_ext
    change oldValue D ((μ₁ ▷ FZ) ≫ μ₂ ≫ a) =
      oldValue D ((α_ FX FY FZ).hom ≫ (FX ◁ μ₃) ≫ μ₄)
    erw [oldValue_comp D (μ₁ ▷ FZ) (μ₂ ≫ a), oldValue_comp D μ₂ a,
      oldValue_comp D (α_ FX FY FZ).hom ((FX ◁ μ₃) ≫ μ₄),
      oldValue_comp D (FX ◁ μ₃) μ₄,
      oldValue_whiskerRight D μ₁ FZ, oldValue_whiskerLeft D FX μ₃,
      oldValue_associator D FX FY FZ,
      oldValue_map (ofOldEquivalenceForward E) (α_ X Y Z).hom,
      oldValue_associator C X Y Z]
    dsimp only [μ₁, μ₂, μ₃, μ₄, d, ofOldMonoidalSuperequivalenceData]
    erw [oldValue_iso, oldValue_iso, oldValue_iso, oldValue_iso]
    have h := E.laws.forward.associativity X Y Z
    simp only [D.laws.comp_assoc] at h
    exact h
  left_unit X := by
    let F := Superfunctor.enriched (ofOldSuperfunctor (ofOldEquivalenceForward E))
    let d := ofOldMonoidalSuperequivalenceData E
    let FX : Even (ofOldSupercategory D) := evenObj _ (E.data.forward.obj X)
    let u := d.unitIso.hom
    let μ := (d.tensorIso (𝟙_ (Even (ofOldSupercategory C))) X).hom
    let a := F.forget.map (λ_ X).hom
    apply (evenHomEquiv D _ _).injective
    apply WideSubcategory.hom_ext
    change oldValue D ((u ▷ FX) ≫ μ ≫ a) = oldValue D (λ_ FX).hom
    erw [oldValue_comp D (u ▷ FX) (μ ≫ a), oldValue_comp D μ a,
      oldValue_whiskerRight D u FX, oldValue_leftUnitor D FX,
      oldValue_map (ofOldEquivalenceForward E) (λ_ X).hom, oldValue_leftUnitor C X]
    dsimp only [u, μ, d, ofOldMonoidalSuperequivalenceData]
    erw [oldValue_iso, oldValue_iso]
    have h := E.laws.forward.left_unit X
    simp only [D.laws.comp_assoc] at h
    exact h
  right_unit X := by
    let F := Superfunctor.enriched (ofOldSuperfunctor (ofOldEquivalenceForward E))
    let d := ofOldMonoidalSuperequivalenceData E
    let FX : Even (ofOldSupercategory D) := evenObj _ (E.data.forward.obj X)
    let u := d.unitIso.hom
    let μ := (d.tensorIso X (𝟙_ (Even (ofOldSupercategory C)))).hom
    let a := F.forget.map (ρ_ X).hom
    apply (evenHomEquiv D _ _).injective
    apply WideSubcategory.hom_ext
    change oldValue D ((FX ◁ u) ≫ μ ≫ a) = oldValue D (ρ_ FX).hom
    erw [oldValue_comp D (FX ◁ u) (μ ≫ a), oldValue_comp D μ a,
      oldValue_whiskerLeft D FX u, oldValue_rightUnitor D FX,
      oldValue_map (ofOldEquivalenceForward E) (ρ_ X).hom, oldValue_rightUnitor C X]
    dsimp only [u, μ, d, ofOldMonoidalSuperequivalenceData]
    erw [oldValue_iso, oldValue_iso]
    have h := E.laws.forward.right_unit X
    simp only [D.laws.comp_assoc] at h
    exact h

def ofOldMonoidalSuperequivalence :
    MonoidalSuperequivalence (ofOldMonoidalSupercategory C) (ofOldMonoidalSupercategory D) :=
  ⟨ofOldMonoidalSuperequivalenceData E, ofOldMonoidalSuperequivalenceLaws E⟩

end RMod.Legacy.Hierarchy
