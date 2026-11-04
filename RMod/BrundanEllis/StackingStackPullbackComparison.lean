import RMod.BrundanEllis.StackingStackRestrictionMonoidal
import RMod.BrundanEllis.StackingMonoidalComparison

/-! Identify the actual diagonal stack with the prescribed closed cochain formula.
The only remaining assumptions are the explicit finite reference hexagon equations. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
attribute [local irreducible] stack stackRestriction stackRestrictionMonoidal

/-- Complete the same fully faithful, essentially surjective, monoidal comparison. -/
def stackRestrictionSuperequivalence (s t : Twist) (h : s.group = t.group)
    (hl : ∀ b c d, ReferenceCommutor.LeftEquation b c d)
    (hr : ∀ b c d, ReferenceCommutor.RightEquation b c d) :
    MonoidalSuperequivalence (stack s t h) (pullback (diagonalRestrictedTwist s t h).val) := by
  letI := stackRestriction_isEquivalence s t h
  exact monoidalSuperequivalenceOfFullyFaithful (stackRestriction s t h)
    (stackRestrictionMonoidal s t h hl hr) (stackRestriction_bijective s t h)
    (tensor_naturality_total (stackRestriction s t h) (stackRestrictionMonoidal s t h hl hr)
      (stackRestrictionMonoidal_enriched s t h hl hr))

/-- The resulting target is exactly twistMul, with its fixed cochain formula. -/
theorem stack_pullback_of_reference_hexagons {G : FiniteGrp.{0}} (s t : TwistOn G)
    (hl : ∀ b c d, ReferenceCommutor.LeftEquation b c d)
    (hr : ∀ b c d, ReferenceCommutor.RightEquation b c d) :
    MonoidallySuperequivalent (stack s.val t.val (s.property.trans t.property.symm))
      (pullback (twistMul s t).val) := by
  have he : MonoidallySuperequivalent (stack s.val t.val (s.property.trans t.property.symm))
      (pullback (diagonalRestrictedTwist s.val t.val (s.property.trans t.property.symm)).val) :=
    ⟨stackRestrictionSuperequivalence s.val t.val (s.property.trans t.property.symm) hl hr⟩
  exact (congrArg (fun u : Twist =>
    MonoidallySuperequivalent (stack s.val t.val (s.property.trans t.property.symm))
      (pullback u)) (diagonalRestrictedTwist_eq_mul s t)).mp he

end RMod.BrundanEllis.Stacking
