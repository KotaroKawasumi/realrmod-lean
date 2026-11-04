import RMod.Enriched.SuperSurface
import RMod.Statement.Gauge

/-! Twists and normalized gauges retain exactly the same computational data
under the old and new declaration layouts. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.EnrichedBridge

def toTwistData (s : TwistData) : StatementLegacy.TwistData :=
  ⟨s.group, s.rho, s.nu, s.omega⟩
def fromTwistData (s : StatementLegacy.TwistData) : TwistData :=
  ⟨s.group, s.rho, s.nu, s.omega⟩

def toTwist (s : Twist) : StatementLegacy.Twist :=
  ⟨toTwistData s.toTwistData, ⟨s.nu_one_left, s.nu_one_right,
    s.omega_one₁, s.omega_one₂, s.omega_one₃, s.cocycle, s.pentagon⟩⟩
def fromTwist (s : StatementLegacy.Twist) : Twist :=
  ⟨fromTwistData s.data, s.laws.nu_one_left, s.laws.nu_one_right,
    s.laws.omega_one₁, s.laws.omega_one₂, s.laws.omega_one₃, s.laws.cocycle, s.laws.pentagon⟩

@[simp] theorem to_from_twist (s : StatementLegacy.Twist) : toTwist (fromTwist s) = s := rfl
@[simp] theorem from_to_twist (s : Twist) : fromTwist (toTwist s) = s := rfl

def toGauge (s : Twist) (g : Gauge s.toTwistData) : StatementLegacy.Gauge (toTwist s).data :=
  ⟨⟨g.targetGroup, g.phi, g.lam, g.beta⟩, ⟨g.lam_one, g.beta_one_left, g.beta_one_right⟩⟩
def fromGauge (s : Twist) (g : StatementLegacy.Gauge (toTwist s).data) : Gauge s.toTwistData :=
  ⟨⟨g.data.targetGroup, g.data.phi, g.data.lam, g.data.beta⟩,
    g.laws.lam_one, g.laws.beta_one_left, g.laws.beta_one_right⟩

/-- Valid-twist gauge reachability is the same explicitly computed relation. -/
theorem gauge_iff (s t : Twist) : GaugeEquivalent s t ↔
    StatementLegacy.GaugeEquivalent (toTwist s).data (toTwist t).data := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨toGauge s g, ?_⟩
    rw [gaugeTransform_data] at hg
    exact congrArg toTwistData hg
  · rintro ⟨g, hg⟩
    refine ⟨fromGauge s g, ?_⟩
    rw [gaugeTransform_data]
    exact congrArg fromTwistData hg

end RMod.EnrichedBridge
