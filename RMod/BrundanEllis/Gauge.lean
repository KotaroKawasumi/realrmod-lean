import RMod.BrundanEllis.TwistSurface
import RMod.Enriched.SuperSurface

/-! Completed gauge moves reuse the verified cochain calculations.
Both conversions retain the finite group, its homomorphism and all cochains. -/
noncomputable section
set_option autoImplicit false
namespace RMod.BrundanEllis
namespace Bridge

def toTwistData (s : TwistData) : RMod.TwistData := ⟨s.group, s.rho, s.nu, s.omega⟩
def fromTwistData (s : RMod.TwistData) : TwistData := ⟨s.group, s.rho, s.nu, s.omega⟩
def toTwist (s : Twist) : RMod.Twist :=
  ⟨toTwistData s.toTwistData, s.nu_one_left, s.nu_one_right,
    s.omega_one₁, s.omega_one₂, s.omega_one₃, s.cocycle, s.pentagon⟩
def fromTwist (s : RMod.Twist) : Twist :=
  ⟨fromTwistData s.toTwistData, s.nu_one_left, s.nu_one_right,
    s.omega_one₁, s.omega_one₂, s.omega_one₃, s.cocycle, s.pentagon⟩

@[simp] theorem to_from_twist (s : RMod.Twist) : toTwist (fromTwist s) = s := rfl
@[simp] theorem from_to_twist (s : Twist) : fromTwist (toTwist s) = s := rfl

def toGauge (s : Twist) (g : Gauge s.toTwistData) : RMod.Gauge (toTwist s).toTwistData :=
  ⟨⟨g.targetGroup, g.phi, g.lam, g.beta⟩, g.lam_one, g.beta_one_left, g.beta_one_right⟩
def fromGauge (s : Twist) (g : RMod.Gauge (toTwist s).toTwistData) : Gauge s.toTwistData :=
  ⟨⟨g.targetGroup, g.phi, g.lam, g.beta⟩, g.lam_one, g.beta_one_left, g.beta_one_right⟩
end Bridge

/-- A normalized gauge move lands in Twist; its computational data are fixed below. -/
def gaugeTransform (s : Twist) (g : Gauge s.toTwistData) : Twist :=
  Bridge.fromTwist (RMod.gaugeTransform (Bridge.toTwist s) (Bridge.toGauge s g))
/-- The completed move uses exactly the specified cochain formulas. -/
theorem gaugeTransform_data (s : Twist) (g : Gauge s.toTwistData) :
    (gaugeTransform s g).toTwistData = gaugeTransformData s.toTwistData g.toGaugeData := by
  change Bridge.fromTwistData
    (RMod.gaugeTransform (Bridge.toTwist s) (Bridge.toGauge s g)).toTwistData = _
  rw [RMod.gaugeTransform_data]
  rfl

/-- Gauge reachability is a relation on valid twists, comparing only their computational data. -/
abbrev GaugeEquivalent (s t : Twist) : Prop :=
  ∃ g : Gauge s.toTwistData, (gaugeTransform s g).toTwistData = t.toTwistData

namespace Bridge
/-- The gauge criterion retains exactly the old computed reachability relation. -/
theorem gauge_iff (s t : Twist) : GaugeEquivalent s t ↔
    RMod.GaugeEquivalent (toTwist s) (toTwist t) := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨toGauge s g, ?_⟩
    rw [gaugeTransform_data] at hg
    rw [RMod.gaugeTransform_data]
    exact congrArg toTwistData hg
  · rintro ⟨g, hg⟩
    refine ⟨fromGauge s g, ?_⟩
    rw [gaugeTransform_data]
    rw [RMod.gaugeTransform_data] at hg
    exact congrArg fromTwistData hg
end Bridge
end RMod.BrundanEllis
