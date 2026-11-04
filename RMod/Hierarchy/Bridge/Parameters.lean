import RMod.Hierarchy.Abstract.Parameters
import RMod.Classification.Abstract.Parameters

/-!
# Parameter transport to the proved classification

The group, type homomorphism, and all cochains are retained exactly.
Only the surrounding structure names change. The round-trip identities
and gauge criterion below ensure that transport does not alter parameters.
-/

set_option autoImplicit false
namespace RMod.Legacy

def TwistData.toOld (t : TwistData) : Classification.TwistData :=
  ⟨t.group, t.rho, t.nu, t.omega⟩

def TwistData.ofOld (t : Classification.TwistData) : TwistData :=
  ⟨t.group, t.rho, t.nu, t.omega⟩

theorem TwistLaws.toOld {t : TwistData} (h : TwistLaws t) :
    Classification.TwistLaws t.toOld :=
  ⟨h.nu_one_left, h.nu_one_right, h.omega_one₁, h.omega_one₂, h.omega_one₃,
    h.cocycle, h.pentagon⟩

theorem TwistLaws.ofOld {t : Classification.TwistData} (h : Classification.TwistLaws t) :
    TwistLaws (TwistData.ofOld t) :=
  ⟨h.nu_one_left, h.nu_one_right, h.omega_one₁, h.omega_one₂, h.omega_one₃,
    h.cocycle, h.pentagon⟩

def Twist.toOld (t : Twist) : Classification.Twist := ⟨t.data.toOld, t.laws.toOld⟩
def Twist.ofOld (t : Classification.Twist) : Twist :=
  ⟨TwistData.ofOld t.data, TwistLaws.ofOld t.laws⟩

@[simp] theorem TwistData.ofOld_toOld (t : TwistData) : ofOld t.toOld = t := rfl
@[simp] theorem TwistData.toOld_ofOld (t : Classification.TwistData) : (ofOld t).toOld = t := rfl
@[simp] theorem Twist.ofOld_toOld (t : Twist) : ofOld t.toOld = t := rfl
@[simp] theorem Twist.toOld_ofOld (t : Classification.Twist) : (ofOld t).toOld = t := rfl

def GaugeData.toOld {s t : TwistData} (g : GaugeData s t) :
    Classification.GaugeData s.toOld t.toOld := ⟨g.phi, g.lam, g.beta⟩

def GaugeData.ofOld {s t : TwistData} (g : Classification.GaugeData s.toOld t.toOld) :
    GaugeData s t := ⟨g.phi, g.lam, g.beta⟩

theorem GaugeLaws.toOld {s t : TwistData} {g : GaugeData s t} (h : GaugeLaws s t g) :
    Classification.GaugeLaws s.toOld t.toOld g.toOld :=
  ⟨h.rho, h.lam_one, h.beta_one_left, h.beta_one_right, h.nu, h.omega⟩

theorem GaugeLaws.ofOld {s t : TwistData} {g : Classification.GaugeData s.toOld t.toOld}
    (h : Classification.GaugeLaws s.toOld t.toOld g) :
    GaugeLaws s t (GaugeData.ofOld g) :=
  ⟨h.rho, h.lam_one, h.beta_one_left, h.beta_one_right, h.nu, h.omega⟩

def Gauge.toOld {s t : TwistData} (g : Gauge s t) :
    Classification.Gauge s.toOld t.toOld := ⟨g.data.toOld, g.laws.toOld⟩

def Gauge.ofOld {s t : TwistData} (g : Classification.Gauge s.toOld t.toOld) : Gauge s t :=
  ⟨GaugeData.ofOld g.data, GaugeLaws.ofOld g.laws⟩

theorem gaugeEquivalent_iff_old (s t : TwistData) :
    GaugeEquivalent s t ↔ Classification.GaugeEquivalent s.toOld t.toOld :=
  ⟨fun ⟨g⟩ => ⟨g.toOld⟩, fun ⟨g⟩ => ⟨Gauge.ofOld g⟩⟩

end RMod.Legacy
