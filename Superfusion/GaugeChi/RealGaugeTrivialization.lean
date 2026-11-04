/-
Superfusion / GaugeChi / RealGaugeTrivialization

Assembly of the real regular trivialization from the LEAN-gauge table
certificate (`RealGaugeTrivializationTable.lean`).

The certgen pipeline computes `realGauge`'s own connector parities as the
172-odd table `realLeanParityTable`. The identification obligations are
stated directly against those semantic tables — the ones the
explicit-connector program (Ttab through the `ConnectorFamily` API)
actually discharges:

* `hp`: the canonical parity equals the Lean-gauge parity table — this
  is `ConnectorFamily.parity_eq` at a certificate family whose parity
  field is `realLeanParityTable`;
* `hχ`: the canonical pentagon scalar agrees with the Lean-gauge `χ`
  table up to an explicit coboundary — by `chiOfFamily_rescale_dm₃`
  this follows from `chiOfFamily (Ttab) = realLeanChiTable` pushed
  along `dyadicHom`.
-/
import Superfusion.Category.RegularData
import Superfusion.Gauge.RealGaugeInstance
import Superfusion.GaugeChi.RealGaugeTrivializationTable
import Superfusion.Cochain.RegularTrivializationTransport

namespace Superfusion

namespace GaugeChi

/-- The real regular trivialization from the Lean-gauge certificate,
conditional on the two identification obligations. -/
noncomputable def realRegularTrivializationLean
    (hp : ∀ a b c, gParityCochain ℝ realGauge a b c = realLeanParityTable a b c)
    (γ : Multiplicative (ZMod 8) → Multiplicative (ZMod 8) →
      Multiplicative (ZMod 8) → ℝˣ)
    (hχ : ∀ a b c d,
      gChiCanonCochain ℝ realGauge a b c d =
        dyadicHom ℝ (realLeanChiTable a b c d) * dm₃ γ a b c d) :
    realGauge.RegularTrivialization ℝ :=
  (((realLeanTableTrivialization.map (dyadicHom ℝ) (dyadicHom_sign ℝ)).ofCoboundary
        (gChiCanonCochain ℝ realGauge) γ hχ).copy
    (gParityCochain ℝ realGauge) (gChiCanonCochain ℝ realGauge)
    hp (fun _ _ _ _ => rfl))

end GaugeChi

end Superfusion
