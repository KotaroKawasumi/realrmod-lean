import Mathlib

/-! Fixed twist and gauge definitions from the Challenge declaration surface.
The completed declaration forms use the shared-surface Data--Laws exception. -/
noncomputable section
set_option autoImplicit false
namespace RMod.BrundanEllis

/-! Twists and gauges use Mathlib finite groups, homomorphisms, and units. -/
def realSign (a : ZMod 2) : ℝˣ := if a = 0 then 1 else -1

structure TwistData where
  group : FiniteGrp.{0}
  rho : group →* Multiplicative (ZMod 8)
  nu : group → group → ZMod 2
  omega : group → group → group → ℝˣ

/-- Finite group data and normalized cochains satisfying the signed pentagon equation. -/
structure Twist extends TwistData where
  nu_one_left : ∀ g, nu 1 g = 0
  nu_one_right : ∀ g, nu g 1 = 0
  omega_one₁ : ∀ g h, omega 1 g h = 1
  omega_one₂ : ∀ g h, omega g 1 h = 1
  omega_one₃ : ∀ g h, omega g h 1 = 1
  cocycle : ∀ g h k,
    nu h k + nu (g * h) k + nu g (h * k) + nu g h = 0
  pentagon : ∀ g h k l,
    omega h k l * omega g (h * k) l * omega g h k =
      realSign (nu g h * nu k l) *
        (omega (g * h) k l * omega g h (k * l))

/-! A gauge specifies a move from one source; its target cochains are computed. -/
structure GaugeData (s : TwistData) where
  targetGroup : FiniteGrp.{0}
  phi : s.group ≃* targetGroup
  lam : s.group → ZMod 2
  beta : s.group → s.group → ℝˣ
/-- Normalized gauges retain their raw data and add only the three normalization laws. -/
structure Gauge (s : TwistData) extends GaugeData s where
  lam_one : lam 1 = 0
  beta_one_left : ∀ g, beta 1 g = 1
  beta_one_right : ∀ g, beta g 1 = 1

/-- Compute the target, using the new binary cochain in the signed omega formula. -/
@[implicit_reducible] def gaugeTransformData (s : TwistData) (d : GaugeData s) : TwistData :=
  let nu g h := s.nu g h + d.lam h + d.lam (g * h) + d.lam g
  { group := d.targetGroup
    rho := s.rho.comp d.phi.symm.toMonoidHom
    nu x y := nu (d.phi.symm x) (d.phi.symm y)
    omega x y z :=
      let g := d.phi.symm x
      let h := d.phi.symm y
      let k := d.phi.symm z
      s.omega g h k * (d.beta (g * h) k * d.beta g h) *
        (d.beta h k * d.beta g (h * k))⁻¹ *
        realSign (nu g h * d.lam k + d.lam g * s.nu h k) }

end RMod.BrundanEllis
