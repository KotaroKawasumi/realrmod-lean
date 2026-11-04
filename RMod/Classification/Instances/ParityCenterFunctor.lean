import RMod.Classification.Instances.ParityFactorCenter
import Mathlib.CategoryTheory.Monoidal.Discrete

/-!
# The parity-factor functor to the Drinfeld center

Use Mathlib's discrete monoidal category of the additive parity group,
expressed multiplicatively to distinguish its group operation from ring
multiplication. The object map is the actual central factor, and the maps
of the discrete source are the canonical equality comparisons.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory Superfusion.Category

noncomputable def parityCenterFunctor (C : WeaklyPointedSuperfusion.{u, v})
    (p : PiData C.data) (hp : PiLaws C.data p) :
    Discrete (Multiplicative (ZMod 2)) ⥤ Center (EvenSubcategory ℝ (LinearCategory C)) :=
  Discrete.functor (fun a => factorCenter C p hp (Multiplicative.toAdd a))

end RMod.Classification
