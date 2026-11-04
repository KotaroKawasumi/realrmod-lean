import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import RMod.Classification.Proofs.Parameters
import RMod.Classification.Proofs.GaugeRatioScalars

/-!
# Compatibility of source-indexed gauge moves with the proved classification

The source-indexed action is compared with the established two-endpoint relation.
All cochain formulas and their normalization conventions are retained.

The target is computed from the source, an output group isomorphism, and normalized
cochains. The full signed pentagon is preserved, and reachability is equivalent to
the legacy two-endpoint relation. Existing classification and sign normalization
proofs are reused through this equivalence.
-/

set_option autoImplicit false
noncomputable section
namespace RMod.GaugeRevision
open Classification

/-! A gauge specifies a move from one source; its target cochains are computed. -/
structure GaugeData (s : TwistData) where
  targetGroup : FiniteGrp.{0}
  phi : s.group ≃* targetGroup
  lam : s.group → ZMod 2
  beta : s.group → s.group → ℝˣ
structure GaugeLaws {s : TwistData} (d : GaugeData s) : Prop where
  lam_one : d.lam 1 = 0
  beta_one_left : ∀ g, d.beta 1 g = 1
  beta_one_right : ∀ g, d.beta g 1 = 1
structure Gauge (s : TwistData) where
  data : GaugeData s
  laws : GaugeLaws data

/-- Compute the target, using the new binary cochain in the signed omega formula. -/
@[implicit_reducible] def gaugeTransformData (s : TwistData) (d : GaugeData s) : TwistData :=
  let nu g h := s.nu g h + d.lam h + d.lam (g * h) + d.lam g
  { group := d.targetGroup
    rho := s.rho.comp d.phi.symm.toMonoidHom
    nu := fun x y => nu (d.phi.symm x) (d.phi.symm y)
    omega := fun x y z =>
      let g := d.phi.symm x
      let h := d.phi.symm y
      let k := d.phi.symm z
      s.omega g h k * (d.beta (g * h) k * d.beta g h) *
        (d.beta h k * d.beta g (h * k))⁻¹ *
        realSign (nu g h * d.lam k + d.lam g * s.nu h k) }

/-- Reachability is equality with the explicitly computed target data. -/
def GaugeEquivalent (s t : TwistData) : Prop :=
  ∃ g : Gauge s, gaugeTransformData s g.data = t

private def newNu (s : TwistData) (lam : s.group → ZMod 2) (g h : s.group) : ZMod 2 :=
  s.nu g h + lam h + lam (g * h) + lam g
private def signExponent (s : TwistData) (lam : s.group → ZMod 2) (g h k : s.group) : ZMod 2 :=
  newNu s lam g h * lam k + lam g * s.nu h k
private def ratio {G : Type} [Group G] (beta : G → G → ℝˣ) (g h k : G) : ℝˣ :=
  (beta (g * h) k * beta g h) * (beta h k * beta g (h * k))⁻¹

private theorem newNu_cocycle (s : TwistData) (hs : TwistLaws s)
    (lam : s.group → ZMod 2) (g h k : s.group) :
    newNu s lam h k + newNu s lam (g * h) k +
      newNu s lam g (h * k) + newNu s lam g h = 0 := by
  dsimp [newNu]
  simp only [mul_assoc]
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hs.cocycle g h k

private theorem signExponent_coboundary (s : TwistData) (hs : TwistLaws s)
    (lam : s.group → ZMod 2) (g h k l : s.group) :
    signExponent s lam h k l + signExponent s lam g (h * k) l + signExponent s lam g h k +
      s.nu g h * s.nu k l =
    newNu s lam g h * newNu s lam k l +
      signExponent s lam (g * h) k l + signExponent s lam g h (k * l) := by
  dsimp [signExponent, newNu]
  simp only [mul_assoc]
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
    lam l * hs.cocycle g h k + lam g * hs.cocycle h k l

private theorem ratio_cocycle {G : Type} [Group G] (beta : G → G → ℝˣ) (g h k l : G) :
    ratio beta h k l * ratio beta g (h * k) l * ratio beta g h k =
      ratio beta (g * h) k l * ratio beta g h (k * l) := by
  dsimp [ratio]
  simp only [mul_assoc]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private def newOmega (s : TwistData) (lam : s.group → ZMod 2)
    (beta : s.group → s.group → ℝˣ) (g h k : s.group) : ℝˣ :=
  s.omega g h k * (beta (g * h) k * beta g h) * (beta h k * beta g (h * k))⁻¹ *
    realSign (signExponent s lam g h k)

private theorem newOmega_pentagon (s : TwistData) (hs : TwistLaws s)
    (lam : s.group → ZMod 2) (beta : s.group → s.group → ℝˣ) (g h k l : s.group) :
    newOmega s lam beta h k l * newOmega s lam beta g (h * k) l * newOmega s lam beta g h k =
      realSign (newNu s lam g h * newNu s lam k l) *
        (newOmega s lam beta (g * h) k l * newOmega s lam beta g h (k * l)) := by
  let E := signExponent s lam
  have he := congrArg realSign (signExponent_coboundary s hs lam g h k l)
  change realSign (E h k l + E g (h * k) l + E g h k + s.nu g h * s.nu k l) =
    realSign (newNu s lam g h * newNu s lam k l + E (g * h) k l + E g h (k * l)) at he
  simp only [realSign_add] at he
  calc
    _ = (s.omega h k l * s.omega g (h * k) l * s.omega g h k) *
        (ratio beta h k l * ratio beta g (h * k) l * ratio beta g h k) *
        (realSign (E h k l) * realSign (E g (h * k) l) * realSign (E g h k)) := by
          dsimp [newOmega, ratio, E]
          ac_rfl
    _ = (s.omega (g * h) k l * s.omega g h (k * l)) *
        (ratio beta (g * h) k l * ratio beta g h (k * l)) *
        (realSign (E h k l) * realSign (E g (h * k) l) * realSign (E g h k) *
          realSign (s.nu g h * s.nu k l)) := by
          rw [hs.pentagon, ratio_cocycle]
          ac_rfl
    _ = _ := by
      rw [he]
      dsimp [newOmega, ratio, E]
      ac_rfl

/-- Normalized moves preserve every Twist law, including the signed pentagon. -/
theorem gaugeTransformLaws (s : Twist) (g : Gauge s.data) :
    TwistLaws (gaugeTransformData s.data g.data) where
  nu_one_left x := by
    simp [gaugeTransformData, s.laws.nu_one_left, g.laws.lam_one, CharTwo.add_self_eq_zero]
  nu_one_right x := by
    simp [gaugeTransformData, s.laws.nu_one_right, g.laws.lam_one, CharTwo.add_self_eq_zero]
  omega_one₁ x y := by
    simp [gaugeTransformData, s.laws.nu_one_left, s.laws.omega_one₁,
      g.laws.lam_one, g.laws.beta_one_left, realSign, CharTwo.add_self_eq_zero]
  omega_one₂ x y := by
    simp [gaugeTransformData, s.laws.nu_one_left, s.laws.nu_one_right, s.laws.omega_one₂,
      g.laws.lam_one, g.laws.beta_one_left, g.laws.beta_one_right, realSign, CharTwo.add_self_eq_zero]
  omega_one₃ x y := by
    simp [gaugeTransformData, s.laws.nu_one_right, s.laws.omega_one₃,
      g.laws.lam_one, g.laws.beta_one_right, realSign]
  cocycle x y z := by
    simpa only [gaugeTransformData, newNu, map_mul] using
      newNu_cocycle s.data s.laws g.data.lam (g.data.phi.symm x) (g.data.phi.symm y) (g.data.phi.symm z)
  pentagon x y z w := by
    simpa only [gaugeTransformData, newOmega, signExponent, newNu, map_mul] using
      newOmega_pentagon s.data s.laws g.data.lam g.data.beta
        (g.data.phi.symm x) (g.data.phi.symm y) (g.data.phi.symm z) (g.data.phi.symm w)

/-- The target is a completed Twist, with exactly the computed data. -/
def gaugeTransform (s : Twist) (g : Gauge s.data) : Twist :=
  ⟨gaugeTransformData s.data g.data, gaugeTransformLaws s g⟩

theorem gaugeTransform_data (s : Twist) (g : Gauge s.data) :
    (gaugeTransform s g).data = gaugeTransformData s.data g.data := rfl

/-- The new move always provides the legacy two-endpoint gauge equations. -/
def Gauge.toOld {s : TwistData} (g : Gauge s) :
    Classification.Gauge s (gaugeTransformData s g.data) where
  data := ⟨g.data.phi, g.data.lam, g.data.beta⟩
  laws := {
    rho := by
      intro x
      change s.rho (g.data.phi.symm (g.data.phi x)) = s.rho x
      rw [MulEquiv.symm_apply_apply]
    lam_one := g.laws.lam_one
    beta_one_left := g.laws.beta_one_left
    beta_one_right := g.laws.beta_one_right
    nu := by
      intro x y
      change newNu s g.data.lam (g.data.phi.symm (g.data.phi x)) (g.data.phi.symm (g.data.phi y)) = _
      simp only [MulEquiv.symm_apply_apply]
      rfl
    omega := by
      intro x y z
      dsimp only [gaugeTransformData]
      simp only [MulEquiv.symm_apply_apply] }

/-- Forget the prescribed endpoint, retaining its group and the normalized cochains. -/
def Gauge.ofOld {s t : TwistData} (g : Classification.Gauge s t) : Gauge s :=
  ⟨⟨t.group, g.data.phi, g.data.lam, g.data.beta⟩,
    ⟨g.laws.lam_one, g.laws.beta_one_left, g.laws.beta_one_right⟩⟩

/-- Computing the endpoint of an old gauge recovers its originally prescribed target. -/
theorem gaugeTransformData_ofOld {s t : TwistData} (g : Classification.Gauge s t) :
    gaugeTransformData s (Gauge.ofOld g).data = t := by
  have hr : (gaugeTransformData s (Gauge.ofOld g).data).rho = t.rho := by
    ext x
    obtain ⟨a, rfl⟩ := g.data.phi.surjective x
    change s.rho (g.data.phi.symm (g.data.phi a)) = t.rho (g.data.phi a)
    rw [MulEquiv.symm_apply_apply]
    exact (g.laws.rho a).symm
  have hn : (gaugeTransformData s (Gauge.ofOld g).data).nu = t.nu := by
    funext x y
    obtain ⟨a, rfl⟩ := g.data.phi.surjective x
    obtain ⟨b, rfl⟩ := g.data.phi.surjective y
    simpa [gaugeTransformData, Gauge.ofOld] using (g.laws.nu a b).symm
  have hw : (gaugeTransformData s (Gauge.ofOld g).data).omega = t.omega := by
    funext x y z
    obtain ⟨a, rfl⟩ := g.data.phi.surjective x
    obtain ⟨b, rfl⟩ := g.data.phi.surjective y
    obtain ⟨c, rfl⟩ := g.data.phi.surjective z
    simpa [gaugeTransformData, Gauge.ofOld, g.laws.nu] using (g.laws.omega a b c).symm
  cases t
  dsimp [gaugeTransformData, Gauge.ofOld] at hr hn hw ⊢
  congr 1

/-- The reformulation preserves the entire old gauge relation, even on raw data. -/
theorem gaugeEquivalent_iff_old (s t : TwistData) :
    GaugeEquivalent s t ↔ Classification.GaugeEquivalent s t := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.toOld⟩
  · rintro ⟨g⟩
    exact ⟨Gauge.ofOld g, gaugeTransformData_ofOld g⟩


end RMod.GaugeRevision
