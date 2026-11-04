import RMod.BrundanEllis.Foundation

/-! Mathlib abelian structure supplies finite biproducts for the fixed even
additive structure. This construction is separate from abstract class definitions. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u
namespace RMod.BrundanEllis

/-- Abelian categories supply finite products; use the fixed even additive structure. -/
instance evenFiniteBiproducts (C : Type u) [SuperCategory C] [Abelian (Even C)] :
    HasFiniteBiproducts (Even C) :=
  HasFiniteBiproducts.of_hasFiniteProducts

end RMod.BrundanEllis
