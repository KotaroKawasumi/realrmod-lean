import RMod.BrundanEllis.StackingDiagonal

/-! The proved diagonal closure specializes the general completion contract.
These auxiliary constructions take an exterior pairing as input; the public
Deligne construction must supply that pairing and its monoidal comparisons. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable (s t : Twist) (φ : s.group ≃* t.group)
  (D : WeaklyPointedFusionPiSuperCat)
  (F : SuperFunctor (SuperTensorProduct (pullback s) (pullback t)) D)
  (M : (evenPair F).CoreMonoidal)

def diagonalInclusion : SuperFunctor (diagonalCompletion s t φ D F M) D := by
  letI := diagonalIsMonoidal s t φ D F M
  exact hullInclusion D (diagonalGenerator s t φ D F)

def diagonalInclusionMonoidal : (diagonalInclusion s t φ D F M).forget.CoreMonoidal := by
  letI := diagonalIsMonoidal s t φ D F M
  exact hullInclusionMonoidal D (diagonalGenerator s t φ D F)

/-- The full enriched inclusion has exactly the completed diagonal as its
essential image and respects tensor products in every homogeneous degree. -/
theorem diagonalCompletion_data :
    let A := diagonalCompletion s t φ D F M
    let J := diagonalInclusion s t φ D F M
    let N := diagonalInclusionMonoidal s t φ D F M
    (∀ X Y a, Function.Bijective (J.map X Y a)) ∧
    (∀ {X X' Y Y'} (f : THom A X X') (g : THom A Y Y'),
      tComp D
        (tTensor (MonoidalSuperCategory.tensor (C := D))
          MonoidalSuperCategory.tensor_objects (tMap J f) (tMap J g))
        (evenPoint (N.μIso X' Y').hom) =
      tComp D (evenPoint (N.μIso X Y).hom)
        (tMap J (tTensor (MonoidalSuperCategory.tensor (C := A))
          MonoidalSuperCategory.tensor_objects f g))) ∧
    (∀ W : Even D,
      (∃ X : Even A, Nonempty (J.forget.obj X ≅ W)) ↔
        AddPiHull D (diagonalGenerator s t φ D F) W) := by
  letI := diagonalIsMonoidal s t φ D F M
  exact ⟨hullInclusion_bijective D _, hullInclusion_tensor_natural D _, hullInclusion_image D _⟩

end RMod.BrundanEllis.Stacking
