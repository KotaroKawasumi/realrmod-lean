import RMod.Classification.Instances.EvenIsos

/-! # Forgetting an even equality map retains its underlying equality map -/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion.Category

theorem even_eqToHom_hom (C : WeaklyPointedSuperfusion.{0, 0})
    {X Y : LinearCategory C} (e : X = Y) :
    (eqToHom (congrArg (evenObj ℝ (LinearCategory C)) e)).hom = (eqToHom e : X ⟶ Y) := by
  cases e
  rfl

end RMod.Classification
