import RMod.BrundanEllis.StackingSurface

/-! The fixed-group gauge relation retains the degree homomorphism.
These bridges compare the actual cochain data, including their dependent group indices. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis
namespace Stacking

/-- All other fields of a completed twist are proof fields. -/
theorem twistData_injective : Function.Injective Twist.toTwistData := by
  intro s t h
  cases s
  cases t
  cases h
  rfl

/-- A normalized gauge with zero parity and unit scalar is the identity move. -/
def identityGauge (s : Twist) : Gauge s.toTwistData :=
  { targetGroup := s.group
    phi := MulEquiv.refl s.group
    lam := fun _ => 0
    beta := fun _ _ => 1
    lam_one := rfl
    beta_one_left := fun _ => rfl
    beta_one_right := fun _ => rfl }

theorem identityGauge_data (s : Twist) :
    (gaugeTransform s (identityGauge s)).toTwistData = s.toTwistData := by
  rw [gaugeTransform_data]
  cases s with
  | mk d h₁ h₂ h₃ h₄ h₅ h₆ h₇ =>
    cases d
    simp [identityGauge, gaugeTransformData, realSign]

end Stacking

/-- The relation includes the identity move without relabeling the group. -/
theorem gaugeEquivalentOn_refl {G : FiniteGrp.{0}} (s : TwistOn G) : GaugeEquivalentOn s s :=
  ⟨Stacking.identityGauge s.val, rfl, rfl, Stacking.identityGauge_data s.val⟩

/-- An identity-label gauge preserves the homomorphism after transport to the fixed group. -/
theorem gaugeEquivalentOn_rho {G : FiniteGrp.{0}} {s t : TwistOn G}
    (h : GaugeEquivalentOn s t) : (s.property ▸ s.val.rho) = (t.property ▸ t.val.rho) := by
  rcases h with ⟨d, hd, hphi, hdata⟩
  rw [gaugeTransform_data] at hdata
  rcases s with ⟨s, hs⟩
  rcases t with ⟨t, ht⟩
  rcases s with ⟨⟨S, r, v, a⟩, s1, s2, s3, s4, s5, s6, s7⟩
  rcases t with ⟨⟨T, q, w, b⟩, t1, t2, t3, t4, t5, t6, t7⟩
  dsimp only at hs ht
  subst S
  subst T
  rcases d with ⟨⟨H, phi, lam, beta⟩, h1, h2, h3⟩
  change H = G at hd
  subst H
  change phi = MulEquiv.refl G at hphi
  subst phi
  simp only [gaugeTransformData, MulEquiv.refl_symm] at hdata
  cases hdata
  rfl

end RMod.BrundanEllis
