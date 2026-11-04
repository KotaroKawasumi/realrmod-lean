import RMod.Hierarchy.Bridge.TotalCategory
import RMod.Classification.Proofs.Endomorphisms

/-!
# The split unit as a real algebra equivalence

The old injectivity and surjectivity of scalar endomorphisms say exactly
that the canonical real algebra map is bijective. Reassembling total
morphisms therefore gives the requested algebra equivalence with R.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory
namespace RMod.Legacy.Hierarchy
variable (C : WeaklyPointedSuperfusion.{0, 0})

def ofOldUnitEndEquiv : End (totalObj (ofOldSupercategory C) C.data.tensorUnit) ≃ₐ[ℝ] ℝ :=
  (totalEndEquiv C C.data.tensorUnit).trans (Classification.unitEndEquiv C).symm

end RMod.Legacy.Hierarchy
