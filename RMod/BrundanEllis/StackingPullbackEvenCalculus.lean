import RMod.BrundanEllis.StackingPullbackHomPoints
import RMod.Hierarchy.Bridge.OldEvenValues

/-! Coordinate and summand formulas for the actual corrected exterior tensor comparison. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
open RMod.Classification RMod.Legacy.Hierarchy

/-- Coordinate maps detect equality of even pullback morphisms. -/
theorem pullbackEvenValue_ext (s : Twist) {X Y : Even (pullback s)} {f g : X ⟶ Y}
    (h : ∀ k, pullbackEvenValue s f k = pullbackEvenValue s g k) : f = g := by
  apply (evenHomEquiv (oldPullback s).toWeaklyPointedSuperfusion X Y).injective
  apply WideSubcategory.hom_ext
  exact funext h

/-- Composition and identities use the original coordinatewise maps. -/
theorem pullbackEvenValue_comp (s : Twist) {X Y Z : Even (pullback s)}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : s.group) :
    pullbackEvenValue s (f ≫ g) k =
      reference.data.comp (pullbackEvenValue s f k) (pullbackEvenValue s g k) :=
  congrFun (oldValue_comp (oldPullback s).toWeaklyPointedSuperfusion f g) k

theorem pullbackEvenValue_id (s : Twist) (X : Even (pullback s)) (k : s.group) :
    pullbackEvenValue s (𝟙 X) k = reference.data.id (X k).val :=
  congrFun (oldValue_id (oldPullback s).toWeaklyPointedSuperfusion X) k

theorem pullbackEvenValue_grade (s : Twist) {X Y : Even (pullback s)} (f : X ⟶ Y) (k : s.group) :
    reference.data.IsHomogeneous 0 (pullbackEvenValue s f k) :=
  (evenHomEquiv (oldPullback s).toWeaklyPointedSuperfusion X Y f).property k

/-- The even tensor is the specified convolution of the coordinate maps. -/
theorem pullbackEvenValue_tensor (s : Twist) {X X' Y Y' : Even (pullback s)}
    (f : X ⟶ X') (g : Y ⟶ Y') (k : s.group) :
    pullbackEvenValue s (f ⊗ₘ g) k =
      convolutionHom reference.data referenceProperty (oldTwist s).data
        (pullbackEvenValue s f) (pullbackEvenValue s g) k := by
  with_unfolding_all
    exact congrFun (oldValue_tensor (oldPullback s).toWeaklyPointedSuperfusion f g) k

/-- The public associator retains the actual chosen convolution associator. -/
theorem pullbackEvenValue_associator (s : Twist) (X Y Z : Even (pullback s)) (k : s.group) :
    pullbackEvenValue s (α_ X Y Z).hom k =
      (convolutionAssociatorData reference.data referenceProperty (oldTwist s).data
        (oldTwist s).laws X Y Z k).hom := by
  with_unfolding_all
    exact congrFun (oldValue_associator (oldPullback s).toWeaklyPointedSuperfusion X Y Z) k

/-- Both public unitors retain the actual chosen convolution unitors. -/
theorem pullbackEvenValue_leftUnitor (s : Twist) (X : Even (pullback s)) (k : s.group) :
    pullbackEvenValue s (λ_ X).hom k =
      (convolutionLeftUnitorData reference.data referenceProperty (oldTwist s).data
        (oldTwist s).laws X k).hom := by
  with_unfolding_all
    exact congrFun (oldValue_leftUnitor (oldPullback s).toWeaklyPointedSuperfusion X) k

theorem pullbackEvenValue_rightUnitor (s : Twist) (X : Even (pullback s)) (k : s.group) :
    pullbackEvenValue s (ρ_ X).hom k =
      (convolutionRightUnitorData reference.data referenceProperty (oldTwist s).data
        (oldTwist s).laws X k).hom := by
  with_unfolding_all
    exact congrFun (oldValue_rightUnitor (oldPullback s).toWeaklyPointedSuperfusion X) k

end RMod.BrundanEllis.Stacking
