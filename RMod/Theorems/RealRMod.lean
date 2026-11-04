import RMod.Theorems.Internal.RealRModLaws

/-!
# The real regular-module superfusion category

This module exposes the proof of the laws and bundles it with the executable
data. The compatibility proof with the legacy construction is kept in
`RMod.Theorems.Internal.RealRModLaws`.
-/

set_option autoImplicit false

namespace RMod

/-- All weakly pointed superfusion laws for the real regular-module data. -/
theorem realRModLaws : WeaklyPointedSuperfusionLaws realRModData := by
  exact Theorems.Internal.realRModLaws

/-- The finite-coordinate real regular module as a weakly pointed
superfusion category. -/
def realRModLegacy : WeaklyPointedSuperfusion where
  data := realRModData
  laws := realRModLaws

end RMod
