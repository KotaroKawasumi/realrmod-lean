/-
Superfusion / GaugeChi / RealGaugeTrivializationTable

The table-level regular trivialization of the LEAN gauge's pair,
kernel-verified: the certgen pipeline's `ν` is normalized with
`δν = p_lean` (512 points), and the pipeline's `β` trivializes the
shifted pentagon scalar `χ_lean · sgn(q(ν,p_lean)) = δβ` (4096 points),
inside the discrete certificate group `± 2^ℤ`.

These are the tables of `realGauge` itself — the pair the identification
obligations `hp`/`hχ` of `RealGaugeTrivialization.lean` refer to. No
retired-gauge table or comparison theorem is imported.

Everything is decided by the kernel (`decide +kernel`); `native_decide`
is not used anywhere on this track.
-/
import Superfusion.Cochain.RegularTrivialization
import Superfusion.GaugeChi.RealGaugeTables

namespace Superfusion

namespace GaugeChi

/-- The Lean-gauge parity shift is normalized. -/
theorem realLeanNuTable_normalized : Normalized₂ realLeanNuTable := by
  decide +kernel

/-- `δν = p_lean` at all 512 triples. -/
theorem realLeanNuTable_parity :
    ∀ a b c, d₂ realLeanNuTable a b c = realLeanParityTable a b c := by
  decide +kernel

/-- `χ_lean · sgn (q(ν, p_lean)) = δβ` at all 4096 quadruples, in the
dyadic certificate group. -/
theorem realLeanTable_pentagon :
    ∀ a b c d,
      realLeanChiTable a b c d *
          sgn (regularQuadratic realLeanNuTable realLeanParityTable a b c d) =
        dm₃ realLeanBetaTable a b c d := by
  decide +kernel

/-- The table-level regular trivialization of the Lean gauge's frozen
pair, over the dyadic certificate group. -/
def realLeanTableTrivialization :
    RegularTrivialization realLeanParityTable realLeanChiTable where
  ν := realLeanNuTable
  β := realLeanBetaTable
  ν_normalized := realLeanNuTable_normalized
  parity := realLeanNuTable_parity
  pentagon := realLeanTable_pentagon

end GaugeChi

end Superfusion
