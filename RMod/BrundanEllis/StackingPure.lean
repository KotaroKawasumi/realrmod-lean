import RMod.BrundanEllis.StackingGroup
import RMod.BrundanEllis.StackingPureArithmetic

/-! Pure degree twists provide order-compatible lifts.  Their eighth power
has trivial coordinates in the revised normalization. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis.Stacking
open Superfusion
variable {G : FiniteGrp.{0}}

def pureTwist (r : G →* Multiplicative (ZMod 8)) : TwistOn G :=
  let d : TwistData := ⟨G, r, fun _ _ => 0, fun _ _ _ => 1⟩
  ⟨⟨d, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    by intros; simp [d], by intros; simp [d, realSign]⟩, rfl⟩

def twistPower (s : TwistOn G) : ℕ → TwistOn G
  | 0 => twistUnit G
  | n + 1 => twistMul (twistPower s n) s

theorem twistPower_class (s : TwistOn G) (n : ℕ) :
    twistClass (twistPower s n) = twistClass s ^ n := by
  induction n with
  | zero => exact (twistClassCommGroup_data s s).2.1.symm
  | succ n ih =>
    rw [twistPower, ← (twistClassCommGroup_data _ _).1, ih, pow_succ]

theorem purePower_data (r : G →* Multiplicative (ZMod 8)) (n : ℕ) :
    fixedRho (twistPower (pureTwist r) n) = r ^ n ∧
    fixedNu (twistPower (pureTwist r) n) = (fun g h => purePowerNu n (r g) (r h)) ∧
    fixedOmega (twistPower (pureTwist r) n) =
      (fun g h k => realSign (purePowerSign n (r g) (r h) (r k))) := by
  induction n with
  | zero => exact ⟨rfl, rfl, by funext g h k; rfl⟩
  | succ n ih =>
    simp only [twistPower, fixedRho_mul, fixedNu_mul, fixedOmega_mul, ih.1, ih.2.1, ih.2.2]
    refine ⟨rfl, ?_, ?_⟩
    · funext g h
      simp [sumNu, cross, pureTwist, fixedRho, fixedNu, purePowerNu]
    · funext g h k
      simp [stackOmega, correction, typeCorrection, cupOne, cross, pureTwist,
        fixedRho, fixedNu, fixedOmega, purePowerSign, map_mul, mul_pow, realSign_add, mul_assoc]

/-- Trivial coordinates give the neutral gauge class. -/
theorem class_eq_one_of_coordinates (s : TwistOn G)
    (hr : fixedRho s = 1) (hv : fixedNu s = fun _ _ => 0)
    (ha : fixedOmega s = fun _ _ _ => 1) : twistClass s = 1 := by
  rw [(twistClassCommGroup_data s s).2.1]
  apply Quot.sound
  apply (gaugeEquivalentOn_iff _ _).mpr
  refine ⟨(fun _ => 0), (fun _ _ => 1), rfl, (fun _ => rfl), (fun _ => rfl), ?_, ?_, ?_⟩
  · exact hr.symm
  · rw [hv]
    funext g h
    with_unfolding_all rfl
  · rw [hv, ha]
    funext g h k
    with_unfolding_all
      simp [fixedOmega, twistUnit, scalarMove, parityFactor, parityMove]

theorem pureTwist_class_pow_eight (r : G →* Multiplicative (ZMod 8)) :
    twistClass (pureTwist r) ^ 8 = 1 := by
  rw [← twistPower_class]
  apply class_eq_one_of_coordinates
  · rw [(purePower_data r 8).1]
    ext g
    change r g ^ 8 = (1 : Multiplicative (ZMod 8))
    with_unfolding_all
      simpa using (pow_card_eq_one (x := r g))
  · rw [(purePower_data r 8).2.1]
    funext g h
    exact purePowerNu_eight (r g) (r h)
  · rw [(purePower_data r 8).2.2]
    funext g h k
    rw [purePowerSign_eight, realSign_zero]

theorem pureTwist_class_pow_even (r : G →* Multiplicative (ZMod 8))
    (h : ∀ g, bwBit (r g) = 0) (n : ℕ) (hn : r ^ n = 1) :
    twistClass (pureTwist r) ^ n = 1 := by
  rw [← twistPower_class]
  apply class_eq_one_of_coordinates
  · exact (purePower_data r n).1.trans hn
  · rw [(purePower_data r n).2.1]
    funext g k
    exact purePowerNu_even n _ _ (h k)
  · rw [(purePower_data r n).2.2]
    funext g k l
    rw [purePowerSign_even n _ _ _ (h g) (h k) (h l), realSign_zero]

/-- The pure lift is annihilated by every exponent annihilating its degree. -/
theorem pureTwist_class_pow (r : G →* Multiplicative (ZMod 8)) (n : ℕ) (hn : r ^ n = 1) :
    twistClass (pureTwist r) ^ n = 1 := by
  classical
  by_cases he : ∀ g, bwBit (r g) = 0
  · exact pureTwist_class_pow_even r he n hn
  · push_neg at he
    obtain ⟨g, hg⟩ := he
    have hng : r g ^ n = 1 := by
      simpa using congrArg (fun f : G →* Multiplicative (ZMod 8) => f g) hn
    obtain ⟨k, hk⟩ := eight_dvd_of_odd_pow (r g) n hg hng
    rw [hk, pow_mul, pureTwist_class_pow_eight, one_pow]

theorem degree_pureTwist (r : G →* Multiplicative (ZMod 8)) :
    degree G (twistClass (pureTwist r)) = r := rfl

end RMod.BrundanEllis.Stacking
