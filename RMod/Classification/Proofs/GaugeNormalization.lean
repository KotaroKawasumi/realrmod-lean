import RMod.Classification.Instances.NormalizedGauge

/-!
# The omega equation forces a common unit value of beta

No unit normalization of the extracted component comparisons is assumed.
Specializing the omega equation at two identities forces both beta unit
restrictions to equal beta(1,1). Dividing by that common value preserves
the multiplicative coboundary and supplies a completed normalized gauge.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (s t : Twist) (d : GaugeData s.data t.data) (hlam : d.lam 1 = 0)
  (hω : ∀ g h k, t.data.omega (d.phi g) (d.phi h) (d.phi k) =
    s.data.omega g h k * (d.beta (g * h) k * d.beta g h) *
      (d.beta h k * d.beta g (h * k))⁻¹ *
      realSign (t.data.nu (d.phi g) (d.phi h) * d.lam k + d.lam g * s.data.nu h k))

include hlam hω

theorem gauge_beta_one_left_constant (g : s.data.group) : d.beta 1 g = d.beta 1 1 := by
  have he := hω 1 1 g
  simp only [map_one, t.laws.omega_one₁, s.laws.omega_one₁, one_mul,
    t.laws.nu_one_left, hlam, zero_mul, zero_add, realSign, ite_true, mul_one] at he
  have hm := congrArg (fun x => x * (d.beta 1 g * d.beta 1 g)) he
  simp only [one_mul, inv_mul_cancel_right] at hm
  exact mul_left_cancel hm

theorem gauge_beta_one_right_constant (g : s.data.group) : d.beta g 1 = d.beta 1 1 := by
  have he := hω g 1 1
  simp only [map_one, t.laws.omega_one₃, s.laws.omega_one₃, mul_one,
    t.laws.nu_one_right, s.laws.nu_one_left, hlam, mul_zero, zero_add,
    realSign, ite_true, one_mul] at he
  have hm := congrArg (fun x => x * (d.beta 1 1 * d.beta g 1)) he
  simp only [one_mul, inv_mul_cancel_right] at hm
  exact (mul_right_cancel hm).symm

omit hlam hω in
theorem normalizedGauge_ratio (g h k : s.data.group) :
    ((normalizedGaugeData d).beta (g * h) k * (normalizedGaugeData d).beta g h) *
      ((normalizedGaugeData d).beta h k * (normalizedGaugeData d).beta g (h * k))⁻¹ =
      (d.beta (g * h) k * d.beta g h) * (d.beta h k * d.beta g (h * k))⁻¹ := by
  let c := (d.beta 1 1)⁻¹
  change ((c * d.beta (g * h) k) * (c * d.beta g h)) *
    ((c * d.beta h k) * (c * d.beta g (h * k)))⁻¹ = _
  rw [mul_mul_mul_comm c (d.beta (g * h) k) c (d.beta g h),
    mul_mul_mul_comm c (d.beta h k) c (d.beta g (h * k)), mul_inv_rev]
  calc
    _ = ((d.beta (g * h) k * d.beta g h) * (d.beta h k * d.beta g (h * k))⁻¹) *
        ((c * c) * (c * c)⁻¹) := by ac_rfl
    _ = _ := by rw [mul_inv_cancel, mul_one]

theorem normalizedGaugeLaws
    (hρ : ∀ g, t.data.rho (d.phi g) = s.data.rho g)
    (hν : ∀ g h, t.data.nu (d.phi g) (d.phi h) =
      s.data.nu g h + d.lam h + d.lam (g * h) + d.lam g) :
    GaugeLaws s.data t.data (normalizedGaugeData d) where
  rho := hρ
  lam_one := hlam
  beta_one_left g := by
    change (d.beta 1 1)⁻¹ * d.beta 1 g = 1
    rw [gauge_beta_one_left_constant s t d hlam hω g, inv_mul_cancel]
  beta_one_right g := by
    change (d.beta 1 1)⁻¹ * d.beta g 1 = 1
    rw [gauge_beta_one_right_constant s t d hlam hω g, inv_mul_cancel]
  nu := hν
  omega g h k := by
    change t.data.omega (d.phi g) (d.phi h) (d.phi k) =
      s.data.omega g h k *
        ((normalizedGaugeData d).beta (g * h) k * (normalizedGaugeData d).beta g h) *
        ((normalizedGaugeData d).beta h k * (normalizedGaugeData d).beta g (h * k))⁻¹ *
        realSign (t.data.nu (d.phi g) (d.phi h) * d.lam k + d.lam g * s.data.nu h k)
    rw [mul_assoc (s.data.omega g h k), normalizedGauge_ratio]
    exact (hω g h k).trans (by rw [mul_assoc (s.data.omega g h k)])

end RMod.Classification
