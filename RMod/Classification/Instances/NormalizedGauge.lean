import RMod.Classification.Abstract.Parameters

/-!
# Removing a common unit value from a gauge comparison cochain

The group isomorphism and parity cochain are unchanged. Divide each
binary comparison by beta(1,1); the separate laws show when this makes
both unit restrictions equal to one and preserves the omega equation.
-/

set_option autoImplicit false

namespace RMod.Classification

def normalizedGaugeData {s t : TwistData} (d : GaugeData s t) : GaugeData s t where
  phi := d.phi
  lam := d.lam
  beta g h := (d.beta 1 1)⁻¹ * d.beta g h

end RMod.Classification
