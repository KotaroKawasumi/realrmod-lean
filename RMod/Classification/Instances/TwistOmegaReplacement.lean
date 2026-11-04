import RMod.Classification.Abstract.Parameters

/-!
# Replacement of the associator cochain

The group, type and parity data are copied unchanged. The completed
replacement is formed only after receiving laws for the new cochain.
-/

set_option autoImplicit false

namespace RMod.Classification

def omegaReplacementData (t : TwistData) (omega : t.group → t.group → t.group → ℝˣ) : TwistData where
  group := t.group
  rho := t.rho
  nu := t.nu
  omega := omega

def omegaReplacement (t : Twist) (omega : t.data.group → t.data.group → t.data.group → ℝˣ)
    (h : TwistLaws (omegaReplacementData t.data omega)) : Twist where
  data := omegaReplacementData t.data omega
  laws := h

end RMod.Classification
