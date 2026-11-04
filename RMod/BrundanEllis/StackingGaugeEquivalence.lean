import RMod.BrundanEllis.StackingGaugeCalculus

/-! Fixed-label gauges are closed under inverse and composition.  The quotient
uses the original one-step reachability relation, without replacing it by a closure. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis
open Stacking

/-- Reversing an identity-label gauge still fixes the group labels. -/
theorem gaugeEquivalentOn_symm {G : FiniteGrp.{0}} {s t : TwistOn G}
    (h : GaugeEquivalentOn s t) : GaugeEquivalentOn t s := by
  rcases s with ⟨s, hs⟩
  rcases t with ⟨t, ht⟩
  rcases h with ⟨d, hd, hp, he⟩
  have he' := twistData_injective he
  dsimp only at he'
  subst t
  rcases d with ⟨⟨H, p, l, b⟩, hl, hb₁, hb₂⟩
  change H = s.group at hd
  subst H
  change p = MulEquiv.refl s.group at hp
  subst p
  change l 1 = 0 at hl
  change ∀ g, b 1 g = 1 at hb₁
  change ∀ g, b g 1 = 1 at hb₂
  let d := labelGauge s l b hl hb₁ hb₂
  let e := labelGauge (gaugeTransform s d) l
    (fun g h => (b g h)⁻¹ * realSign (l g * l h)) hl
    (by intro g; simp [hl, hb₁, realSign])
    (by intro g; simp [hl, hb₂, realSign])
  refine ⟨e, rfl, rfl, ?_⟩
  rw [gaugeTransform_data]
  change gaugeTransformData (gaugeTransform s d).toTwistData
    (labelGaugeData _ l (fun g h => (b g h)⁻¹ * realSign (l g * l h))) = s.toTwistData
  have hd' := gaugeTransform_data s d
  change (gaugeTransform s d).toTwistData =
    gaugeTransformData s.toTwistData (labelGaugeData s.toTwistData l b) at hd'
  with_unfolding_all exact labelGauge_inv s.toTwistData l b

/-- Composition of two normalized moves is again one normalized move. -/
theorem gaugeEquivalentOn_trans {G : FiniteGrp.{0}} {s t u : TwistOn G}
    (hst : GaugeEquivalentOn s t) (htu : GaugeEquivalentOn t u) :
    GaugeEquivalentOn s u := by
  rcases s with ⟨s, hs⟩
  rcases t with ⟨t, ht⟩
  rcases u with ⟨u, hu⟩
  rcases hst with ⟨d, hd, hp, he⟩
  have he' := twistData_injective he
  dsimp only at he'
  subst t
  rcases d with ⟨⟨H, p, l, b⟩, hl, hb₁, hb₂⟩
  change H = s.group at hd
  subst H
  change p = MulEquiv.refl s.group at hp
  subst p
  rcases htu with ⟨e, he, hq, hf⟩
  have hf' := twistData_injective hf
  dsimp only at hf'
  subst u
  rcases e with ⟨⟨K, q, m, c⟩, hm, hc₁, hc₂⟩
  change K = s.group at he
  subst K
  change q = MulEquiv.refl s.group at hq
  subst q
  change l 1 = 0 at hl
  change ∀ g, b 1 g = 1 at hb₁
  change ∀ g, b g 1 = 1 at hb₂
  change m 1 = 0 at hm
  change ∀ g, c 1 g = 1 at hc₁
  change ∀ g, c g 1 = 1 at hc₂
  let f := labelGauge s (fun g => l g + m g)
    (fun g h => b g h * c g h * realSign (m g * l h))
    (by simp [hl, hm])
    (by intro g; simp [hm, hb₁, hc₁, realSign])
    (by intro g; simp [hl, hb₂, hc₂, realSign])
  refine ⟨f, rfl, rfl, ?_⟩
  with_unfolding_all exact (labelGauge_comp s.toTwistData l m b c).symm

/-- Identity-label reachability is already an equivalence relation. -/
theorem gaugeEquivalentOn_equivalence (G : FiniteGrp.{0}) :
    Equivalence (@GaugeEquivalentOn G) :=
  ⟨gaugeEquivalentOn_refl, fun h => gaugeEquivalentOn_symm h,
    fun h k => gaugeEquivalentOn_trans h k⟩

/-- The quotient retains the exact fixed-label relation from Challenge. -/
def twistSetoid (G : FiniteGrp.{0}) : Setoid (TwistOn G) :=
  ⟨GaugeEquivalentOn, gaugeEquivalentOn_equivalence G⟩
abbrev TwistClass (G : FiniteGrp.{0}) := Quot (@GaugeEquivalentOn G)
abbrev twistClass {G : FiniteGrp.{0}} (s : TwistOn G) : TwistClass G := Quot.mk _ s

namespace Stacking

/-- The proof-free quotient surface is definitionally the original setoid quotient. -/
theorem twistClass_carrier_eq (G : FiniteGrp.{0}) :
    TwistClass G = Quotient (twistSetoid G) := rfl

theorem twistClass_mk_eq {G : FiniteGrp.{0}} (s : TwistOn G) :
    twistClass s = Quotient.mk (twistSetoid G) s := rfl

/-! Internal coordinate projections remove dependent transports from quotient
proofs.  They do not add any data or assumptions to the public Challenge. -/
def fixedRho {G : FiniteGrp.{0}} (s : TwistOn G) : G →* Multiplicative (ZMod 8) :=
  s.property ▸ s.val.rho
def fixedNu {G : FiniteGrp.{0}} (s : TwistOn G) : G → G → ZMod 2 :=
  s.property ▸ s.val.nu
def fixedOmega {G : FiniteGrp.{0}} (s : TwistOn G) : G → G → G → ℝˣ :=
  s.property ▸ s.val.omega

/-- Fixed-label reachability expressed in coordinates on the fixed finite group. -/
theorem gaugeEquivalentOn_iff {G : FiniteGrp.{0}} (s t : TwistOn G) :
    GaugeEquivalentOn s t ↔ ∃ (l : G → ZMod 2) (b : G → G → ℝˣ),
      l 1 = 0 ∧ (∀ g, b 1 g = 1) ∧ (∀ g, b g 1 = 1) ∧
      fixedRho t = fixedRho s ∧ fixedNu t = parityMove (fixedNu s) l ∧
      fixedOmega t = scalarMove (fixedNu s) (fixedOmega s) l b := by
  rcases s with ⟨⟨⟨S, r, v, a⟩, s1, s2, s3, s4, s5, s6, s7⟩, hs⟩
  rcases t with ⟨⟨⟨T, q, w, c⟩, t1, t2, t3, t4, t5, t6, t7⟩, ht⟩
  change S = G at hs
  change T = G at ht
  subst S
  subst T
  dsimp only [fixedRho, fixedNu, fixedOmega]
  constructor
  · rintro ⟨d, hd, hp, he⟩
    rw [gaugeTransform_data] at he
    rcases d with ⟨⟨H, p, l, b⟩, hl, hb₁, hb₂⟩
    change H = G at hd
    subst H
    change p = MulEquiv.refl G at hp
    subst p
    refine ⟨l, b, hl, hb₁, hb₂, ?_⟩
    change gaugeTransformData ⟨G, r, v, a⟩ (labelGaugeData ⟨G, r, v, a⟩ l b) =
      ⟨G, q, w, c⟩ at he
    rw [gaugeTransformData_label] at he
    simp only [TwistData.mk.injEq, heq_eq_eq, true_and] at he
    exact ⟨he.1.symm, he.2.1.symm, he.2.2.symm⟩
  · rintro ⟨l, b, hl, hb₁, hb₂, hr, hv, ha⟩
    refine ⟨labelGauge _ l b hl hb₁ hb₂, rfl, rfl, ?_⟩
    rw [gaugeTransform_data]
    change gaugeTransformData ⟨G, r, v, a⟩ (labelGaugeData ⟨G, r, v, a⟩ l b) =
      ⟨G, q, w, c⟩
    rw [gaugeTransformData_label, ← hr, ← hv, ← ha]

theorem fixedNu_one_left {G : FiniteGrp.{0}} (s : TwistOn G) (g : G) : fixedNu s 1 g = 0 := by
  rcases s with ⟨s, hs⟩
  subst G
  exact s.nu_one_left g

theorem fixedNu_one_right {G : FiniteGrp.{0}} (s : TwistOn G) (g : G) : fixedNu s g 1 = 0 := by
  rcases s with ⟨s, hs⟩
  subst G
  exact s.nu_one_right g

theorem fixedNu_cocycle {G : FiniteGrp.{0}} (s : TwistOn G) (g h k : G) :
    Superfusion.d₂ (fixedNu s) g h k = 0 := by
  rcases s with ⟨s, hs⟩
  subst G
  simpa only [fixedNu, Superfusion.d₂, CharTwo.sub_eq_add] using s.cocycle g h k

end Stacking

end RMod.BrundanEllis
