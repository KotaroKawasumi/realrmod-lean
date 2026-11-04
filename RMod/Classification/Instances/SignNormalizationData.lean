import RMod.Classification.Instances.RealScalarMaps
import RMod.Classification.Proofs.FiniteAveraging

/-!
# Data for removing positive associator scalars

The new omega is the sign of the old omega. Its comparison cochain is
the exponential of the explicit finite average of the logarithms. The
group, type map and binary parity cochain are taken directly from t.
-/

set_option autoImplicit false

namespace RMod.Classification

noncomputable def twistLog (t : TwistData) (g h k : t.group) : ℝ :=
  Multiplicative.toAdd (unitLog (t.omega g h k))

noncomputable def twistLogPrimitive (t : TwistData) (g h : t.group) : ℝ :=
  letI := Fintype.ofFinite t.group
  averageThreeCochain (twistLog t) g h

noncomputable def signTwistData (t : TwistData) : TwistData where
  group := t.group
  rho := t.rho
  nu := t.nu
  omega g h k := unitSign (t.omega g h k)

noncomputable def positiveGaugeData (t : TwistData) : GaugeData t (signTwistData t) where
  phi := MulEquiv.refl t.group
  lam _ := 0
  beta g h := unitExp (Multiplicative.ofAdd (twistLogPrimitive t g h))

end RMod.Classification
