import Mathlib

/-! Twist and gauge data for the hierarchical classification interface. -/

noncomputable section
set_option autoImplicit false
namespace RMod.Legacy

def realSign (a : ZMod 2) : ℝˣ := if a = 0 then 1 else -1


structure TwistData where
  group : FiniteGrp.{0}
  rho : group →* Multiplicative (ZMod 8)
  nu : group → group → ZMod 2
  omega : group → group → group → ℝˣ

structure TwistLaws (d : TwistData) : Prop where
  nu_one_left : ∀ g, d.nu 1 g = 0
  nu_one_right : ∀ g, d.nu g 1 = 0
  omega_one₁ : ∀ g h, d.omega 1 g h = 1
  omega_one₂ : ∀ g h, d.omega g 1 h = 1
  omega_one₃ : ∀ g h, d.omega g h 1 = 1
  cocycle : ∀ g h k,
    d.nu h k + d.nu (g * h) k + d.nu g (h * k) + d.nu g h = 0
  pentagon : ∀ g h k l,
    d.omega h k l * d.omega g (h * k) l * d.omega g h k =
      realSign (d.nu g h * d.nu k l) *
        (d.omega (g * h) k l * d.omega g h (k * l))

structure Twist where
  data : TwistData
  laws : TwistLaws data

/-! Gauge directions are fixed as in the manuscript: source to target,
with tensorator `FX ⋆' FY → F(X ⋆ Y)`. -/

structure GaugeData (s t : TwistData) where
  phi : s.group ≃* t.group
  lam : s.group → ZMod 2
  beta : s.group → s.group → ℝˣ

structure GaugeLaws (s t : TwistData) (d : GaugeData s t) : Prop where
  rho : ∀ g, t.rho (d.phi g) = s.rho g
  lam_one : d.lam 1 = 0
  beta_one_left : ∀ g, d.beta 1 g = 1
  beta_one_right : ∀ g, d.beta g 1 = 1
  nu : ∀ g h,
    t.nu (d.phi g) (d.phi h) = s.nu g h + d.lam h + d.lam (g * h) + d.lam g
  omega : ∀ g h k,
    t.omega (d.phi g) (d.phi h) (d.phi k) =
      s.omega g h k *
      (d.beta (g * h) k * d.beta g h) *
      (d.beta h k * d.beta g (h * k))⁻¹ *
      realSign (t.nu (d.phi g) (d.phi h) * d.lam k + d.lam g * s.nu h k)

structure Gauge (s t : TwistData) where
  data : GaugeData s t
  laws : GaugeLaws s t data

def GaugeEquivalent (s t : TwistData) : Prop := Nonempty (Gauge s t)

end RMod.Legacy
