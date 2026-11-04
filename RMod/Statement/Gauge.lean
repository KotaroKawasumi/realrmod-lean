import RMod.Statement.Surface
import RMod.Statement.GaugeLegacy

/-! The source-indexed gauge action preserves laws and the old classification relation. -/

noncomputable section
set_option autoImplicit false
namespace RMod.StatementLegacy

/-- Preserve the finite group and all cochains in the established presentation. -/
def TwistData.toOld (t : TwistData) : Classification.TwistData :=
  ⟨t.group, t.rho, t.nu, t.omega⟩
def TwistData.ofOld (t : Classification.TwistData) : TwistData :=
  ⟨t.group, t.rho, t.nu, t.omega⟩
theorem TwistLaws.toOld {t : TwistData} (h : TwistLaws t) : Classification.TwistLaws t.toOld :=
  ⟨h.nu_one_left, h.nu_one_right, h.omega_one₁, h.omega_one₂, h.omega_one₃, h.cocycle, h.pentagon⟩
theorem TwistLaws.ofOld {t : Classification.TwistData} (h : Classification.TwistLaws t) :
    TwistLaws (TwistData.ofOld t) :=
  ⟨h.nu_one_left, h.nu_one_right, h.omega_one₁, h.omega_one₂, h.omega_one₃, h.cocycle, h.pentagon⟩
def Twist.toOld (t : Twist) : Classification.Twist := ⟨t.data.toOld, t.laws.toOld⟩
def Twist.ofOld (t : Classification.Twist) : Twist := ⟨TwistData.ofOld t.data, TwistLaws.ofOld t.laws⟩

@[simp] theorem TwistData.ofOld_toOld (t : TwistData) : ofOld t.toOld = t := rfl
@[simp] theorem TwistData.toOld_ofOld (t : Classification.TwistData) : (ofOld t).toOld = t := rfl
@[simp] theorem Twist.ofOld_toOld (t : Twist) : ofOld t.toOld = t := rfl
@[simp] theorem Twist.toOld_ofOld (t : Classification.Twist) : (ofOld t).toOld = t := rfl

/-- Retain the chosen target group, coordinate change, and normalized cochains. -/
def Gauge.toRevision {s : TwistData} (g : Gauge s) : GaugeRevision.Gauge s.toOld :=
  ⟨⟨g.data.targetGroup, g.data.phi, g.data.lam, g.data.beta⟩,
    ⟨g.laws.lam_one, g.laws.beta_one_left, g.laws.beta_one_right⟩⟩
def Gauge.ofRevision {s : TwistData} (g : GaugeRevision.Gauge s.toOld) : Gauge s :=
  ⟨⟨g.data.targetGroup, g.data.phi, g.data.lam, g.data.beta⟩,
    ⟨g.laws.lam_one, g.laws.beta_one_left, g.laws.beta_one_right⟩⟩

theorem gaugeTransformLaws (s : Twist) (g : Gauge s.data) :
    TwistLaws (gaugeTransformData s.data g.data) :=
  TwistLaws.ofOld (GaugeRevision.gaugeTransformLaws s.toOld g.toRevision)

/-- Supply the law proof for the fixed gauge formulas. -/
def gaugeTransform (s : Twist) (g : Gauge s.data) : Twist :=
  ⟨gaugeTransformData s.data g.data, gaugeTransformLaws s g⟩
theorem gaugeTransform_data (s : Twist) (g : Gauge s.data) :
    (gaugeTransform s g).data = gaugeTransformData s.data g.data := rfl

/-- The new reachability relation agrees with the previously proved relation. -/
theorem gaugeEquivalent_iff_old (s t : TwistData) :
    GaugeEquivalent s t ↔ Classification.GaugeEquivalent s.toOld t.toOld := by
  rw [← GaugeRevision.gaugeEquivalent_iff_old]
  constructor
  · rintro ⟨g, h⟩
    exact ⟨g.toRevision, congrArg TwistData.toOld h⟩
  · rintro ⟨g, h⟩
    exact ⟨Gauge.ofRevision g, congrArg TwistData.ofOld h⟩

end RMod.StatementLegacy
