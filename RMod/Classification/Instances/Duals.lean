import RMod.Classification.Abstract.Duals
import RMod.Classification.Instances.LinearMonoidal

/-!
# Choosing the dual data and reusing Mathlib rigidity

The original fusion laws supply existence of both duals. Classical choice
is used explicitly to select their objects and pairing maps. The selected
maps are stored in Data before their laws are bundled. The existing super
exact-pairing adapter then gives Mathlib pairings in the even subcategory.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{u, v})

theorem hasExactPairing_iff (X Y : C.data.Obj) :
    C.data.HasExactPairing X Y ↔ Nonempty (DualPairing C X Y) := by
  constructor
  · rintro ⟨η, ε, hη, hε, hright, hleft⟩
    exact ⟨⟨⟨η, ε⟩, ⟨hη, hε, hright, hleft⟩⟩⟩
  · rintro ⟨p⟩
    exact ⟨p.data.coeval, p.data.eval, p.laws.coeval_even, p.laws.eval_even,
      p.laws.snake_right, p.laws.snake_left⟩

noncomputable def dualChoicesData : DualChoicesData C.data where
  rightObj X := (C.laws.has_right_dual X).choose
  leftObj X := (C.laws.has_left_dual X).choose
  rightPairing X := (Classical.choice ((hasExactPairing_iff C _ _).mp
    (C.laws.has_right_dual X).choose_spec)).data
  leftPairing X := (Classical.choice ((hasExactPairing_iff C _ _).mp
    (C.laws.has_left_dual X).choose_spec)).data

theorem dualChoicesLaws : DualChoicesLaws C.data (dualChoicesData C) where
  rightPairing X := (Classical.choice ((hasExactPairing_iff C _ _).mp
    (C.laws.has_right_dual X).choose_spec)).laws
  leftPairing X := (Classical.choice ((hasExactPairing_iff C _ _).mp
    (C.laws.has_left_dual X).choose_spec)).laws

noncomputable def dualChoices : DualChoices C := ⟨dualChoicesData C, dualChoicesLaws C⟩

namespace DualPairing

variable {C} {X Y : C.data.Obj}

def toSuperExactPairing (p : DualPairing C X Y) :
    SuperExactPairing ℝ (C := LinearCategory C) X Y where
  coeval := p.data.coeval
  eval := p.data.eval
  coeval_mem := p.laws.coeval_even
  eval_mem := p.laws.eval_even
  coevaluation_evaluation :=
    (C.laws.comp_assoc _ _ _).symm.trans p.laws.snake_right
  evaluation_coevaluation :=
    (C.laws.comp_assoc _ _ _).symm.trans p.laws.snake_left

@[implicit_reducible]
noncomputable def toEvenPairing (p : DualPairing C X Y) :
    ExactPairing (evenObj ℝ (LinearCategory C) X) (evenObj ℝ (LinearCategory C) Y) :=
  p.toSuperExactPairing.toEven

end DualPairing

namespace DualChoices

variable {C} (d : DualChoices C)

def rightPairing (X : C.data.Obj) : DualPairing C X (d.data.rightObj X) :=
  ⟨d.data.rightPairing X, d.laws.rightPairing X⟩

def leftPairing (X : C.data.Obj) : DualPairing C (d.data.leftObj X) X :=
  ⟨d.data.leftPairing X, d.laws.leftPairing X⟩

/-- Each Mathlib dual retains the chosen object and the chosen exact pairing. -/
@[implicit_reducible]
noncomputable def hasRightDual (X : EvenSubcategory ℝ (LinearCategory C)) : HasRightDual X where
  rightDual := evenObj ℝ (LinearCategory C) (d.data.rightObj X.obj)
  exact := (d.rightPairing X.obj).toEvenPairing

@[implicit_reducible]
noncomputable def hasLeftDual (X : EvenSubcategory ℝ (LinearCategory C)) : HasLeftDual X where
  leftDual := evenObj ℝ (LinearCategory C) (d.data.leftObj X.obj)
  exact := (d.leftPairing X.obj).toEvenPairing

end DualChoices
end RMod.Classification
