/-
Superfusion / Category / RegularData

The canonical `(p, χ)` of a division fusion gauge, exposed as the input of
the regular-category construction.  This deliberately uses the M13
`GaugeChi` cochains; the earlier table-level parity has not been identified
with them.
-/
import Superfusion.Cochain.RegularTrivialization
import Superfusion.Gauge.Unital
import Superfusion.GaugeChi.QuintChain

namespace Superfusion

namespace DivisionFusionGauge

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]

/-- A trivialization of the canonical degree-four pair of `Γ`.  Its group
is the multiplicative wrapper of the gauge's additive label group. -/
abbrev RegularTrivialization (Γ : DivisionFusionGauge K G) :=
  Superfusion.RegularTrivialization
    (GaugeChi.gParityCochain K Γ) (GaugeChi.gChiCanonCochain K Γ)

/-- Obstruction data and invariant unit-column identifications for the
regular construction.  This structure alone does not assert the triangle
axiom.  The shifted-pentagon normalization later rescales its two unit
columns and constructs the required middle-unit face canonically. -/
structure RegularPreData (Γ : DivisionFusionGauge K G) where
  /-- Invariant algebra-and-column unit identifications. -/
  unital : Γ.UnitalNormalization
  /-- A cochain trivialization of the parity and pentagon obstructions. -/
  trivialization : Γ.RegularTrivialization K

end DivisionFusionGauge

end Superfusion
