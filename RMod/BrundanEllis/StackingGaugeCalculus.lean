import RMod.BrundanEllis.StackingInverse
import RMod.BrundanEllis.StackingGauge

/-! Composition and inversion of normalized gauges without changing group labels.
The scalar correction in composition is the cup product of the two parity cochains. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis.Stacking
open Superfusion
variable {G : FiniteGrp.{0}}

/-- The binary cochain after a parity gauge. -/
def parityMove (v : G → G → ZMod 2) (l : G → ZMod 2) (g h : G) : ZMod 2 :=
  v g h + l h + l (g * h) + l g

/-- The inverse multiplicative coboundary used by the public gauge convention. -/
def scalarRatio (b : G → G → ℝˣ) (g h k : G) : ℝˣ :=
  (b (g * h) k * b g h) * (b h k * b g (h * k))⁻¹

def parityFactor (v : G → G → ZMod 2) (l : G → ZMod 2) (g h k : G) : ZMod 2 :=
  parityMove v l g h * l k + l g * v h k

def scalarMove (v : G → G → ZMod 2) (a : G → G → G → ℝˣ)
    (l : G → ZMod 2) (b : G → G → ℝˣ) (g h k : G) : ℝˣ :=
  a g h k * (b (g * h) k * b g h) * (b h k * b g (h * k))⁻¹ *
    realSign (parityFactor v l g h k)

theorem parityMove_comp (v : G → G → ZMod 2) (l m : G → ZMod 2) :
    parityMove (parityMove v l) m = parityMove v (fun g => l g + m g) := by
  funext g h
  simp only [parityMove]
  ring

/-- The defect of adding two parity gauges is the coboundary of m cup l. -/
theorem parityFactor_comp (v : G → G → ZMod 2) (l m : G → ZMod 2) (g h k : G) :
    parityFactor v l g h k + parityFactor (parityMove v l) m g h k =
      parityFactor v (fun x => l x + m x) g h k +
        d₂ (fun x y => m x * l y) g h k := by
  simp only [parityFactor, parityMove, d₂, CharTwo.sub_eq_add]
  ring_nf
  simp [CharTwo.two_eq_zero]

theorem scalarRatio_mul (b c : G → G → ℝˣ) (g h k : G) :
    scalarRatio (fun x y => b x y * c x y) g h k =
      scalarRatio b g h k * scalarRatio c g h k := by
  simp only [scalarRatio, mul_inv]
  ac_rfl

theorem scalarRatio_sign (f : G → G → ZMod 2) (g h k : G) :
    scalarRatio (fun x y => realSign (f x y)) g h k = realSign (d₂ f g h k) := by
  simp only [scalarRatio, d₂, CharTwo.sub_eq_add, realSign_add, mul_inv, realSign_inv]
  ac_rfl

theorem scalarMove_comp (v : G → G → ZMod 2) (a : G → G → G → ℝˣ)
    (l m : G → ZMod 2) (b c : G → G → ℝˣ) :
    scalarMove (parityMove v l) (scalarMove v a l b) m c =
      scalarMove v a (fun g => l g + m g)
        (fun g h => b g h * c g h * realSign (m g * l h)) := by
  funext g h k
  have hs := congrArg realSign (parityFactor_comp v l m g h k)
  simp only [realSign_add] at hs
  have hm (v : G → G → ZMod 2) (a : G → G → G → ℝˣ)
      (l : G → ZMod 2) (b : G → G → ℝˣ) :
      scalarMove v a l b g h k =
        a g h k * scalarRatio b g h k * realSign (parityFactor v l g h k) := by
    dsimp [scalarMove, scalarRatio]
    ac_rfl
  simp only [hm, scalarRatio_mul, scalarRatio_sign]
  calc
    _ = a g h k * scalarRatio b g h k * scalarRatio c g h k *
        (realSign (parityFactor v l g h k) *
          realSign (parityFactor (parityMove v l) m g h k)) := by ac_rfl
    _ = _ := by rw [hs]; ac_rfl

/-- Identity-label raw gauge data. Normalization is supplied when this is bundled. -/
def labelGaugeData (s : TwistData) (l : s.group → ZMod 2)
    (b : s.group → s.group → ℝˣ) : GaugeData s :=
  ⟨s.group, MulEquiv.refl s.group, l, b⟩

theorem gaugeTransformData_label (s : TwistData) (l : s.group → ZMod 2)
    (b : s.group → s.group → ℝˣ) :
    gaugeTransformData s (labelGaugeData s l b) =
      ⟨s.group, s.rho, parityMove s.nu l, scalarMove s.nu s.omega l b⟩ := by
  with_unfolding_all rfl

/-- Composition is an equality of the actual raw twist data. -/
theorem labelGauge_comp (s : TwistData) (l m : s.group → ZMod 2)
    (b c : s.group → s.group → ℝˣ) :
    let t := gaugeTransformData s (labelGaugeData s l b)
    gaugeTransformData t (labelGaugeData t m c) =
      gaugeTransformData s (labelGaugeData s (fun g => l g + m g)
        (fun g h => b g h * c g h * realSign (m g * l h))) := by
  change (⟨s.group, s.rho, parityMove (parityMove s.nu l) m,
    scalarMove (parityMove s.nu l) (scalarMove s.nu s.omega l b) m c⟩ : TwistData) =
      ⟨s.group, s.rho, parityMove s.nu (fun g => l g + m g),
        scalarMove s.nu s.omega (fun g => l g + m g)
          (fun g h => b g h * c g h * realSign (m g * l h))⟩
  rw [parityMove_comp, scalarMove_comp]

/-- Zero parity and unit scalar give the identity on raw data. -/
theorem labelGauge_zero (s : TwistData) :
    gaugeTransformData s (labelGaugeData s (fun _ => 0) (fun _ _ => 1)) = s := by
  cases s
  simp [gaugeTransformData, labelGaugeData, realSign]

/-- The same parity cochain, with a compensating scalar, reverses a gauge. -/
theorem labelGauge_inv (s : TwistData) (l : s.group → ZMod 2)
    (b : s.group → s.group → ℝˣ) :
    let t := gaugeTransformData s (labelGaugeData s l b)
    gaugeTransformData t (labelGaugeData t l
      (fun g h => (b g h)⁻¹ * realSign (l g * l h))) = s := by
  dsimp only
  rw [labelGauge_comp]
  have hl : (fun g => l g + l g) = (fun _ => 0) := by
    funext g
    exact CharTwo.add_self_eq_zero _
  have hb : (fun g h => b g h * ((b g h)⁻¹ * realSign (l g * l h)) *
      realSign (l g * l h)) = (fun _ _ => 1) := by
    funext g h
    simp [← mul_assoc, realSign_sq]
  rw [hl, hb, labelGauge_zero]

/-- Bundle an identity-label gauge from normalized cochains. -/
def labelGauge (s : Twist) (l : s.group → ZMod 2) (b : s.group → s.group → ℝˣ)
    (hl : l 1 = 0) (hb₁ : ∀ g, b 1 g = 1) (hb₂ : ∀ g, b g 1 = 1) :
    Gauge s.toTwistData :=
  ⟨labelGaugeData s.toTwistData l b, hl, hb₁, hb₂⟩

end RMod.BrundanEllis.Stacking
