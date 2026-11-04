import RMod.BrundanEllis.StackingTypeCoherence
import RMod.BrundanEllis.StackingGaugeEquivalence
import RMod.BrundanEllis.StackingOperationLaws

/-! The specified stacking cochains descend to the original fixed-label gauge
quotient. The group operations and degree map are constructed from these cochains. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis
open Stacking
namespace Stacking
variable {G : FiniteGrp.{0}}

/-- All coordinates of the product, after transporting to G. -/
theorem fixedMul_data (s t : TwistOn G) :
    fixedRho (twistMul s t) = fixedRho s * fixedRho t ∧
    fixedNu (twistMul s t) = sumNu (fixedRho s) (fixedRho t) (fixedNu s) (fixedNu t) ∧
    fixedOmega (twistMul s t) = stackOmega (fixedRho s) (fixedRho t)
      (fixedNu s) (fixedNu t) (fixedOmega s) (fixedOmega t) := by
  rcases s with ⟨⟨⟨S, r, v, a⟩, s1, s2, s3, s4, s5, s6, s7⟩, hs⟩
  rcases t with ⟨⟨⟨T, q, w, b⟩, t1, t2, t3, t4, t5, t6, t7⟩, ht⟩
  change S = G at hs
  change T = G at ht
  subst S
  subst T
  simp [fixedRho, fixedNu, fixedOmega, twistMul, twistMulData, sumNu, cross,
    stackOmega, correction, typeCorrection, add_assoc]
  constructor
  · funext g h
    dsimp [sumNu, cross]
    ring
  · funext g h k
    dsimp [stackOmega, correction, typeCorrection, cross]
    simp only [add_assoc]
    with_unfolding_all rfl

theorem fixedRho_mul (s t : TwistOn G) : fixedRho (twistMul s t) = fixedRho s * fixedRho t :=
  (fixedMul_data s t).1
theorem fixedNu_mul (s t : TwistOn G) :
    fixedNu (twistMul s t) = sumNu (fixedRho s) (fixedRho t) (fixedNu s) (fixedNu t) :=
  (fixedMul_data s t).2.1
theorem fixedOmega_mul (s t : TwistOn G) : fixedOmega (twistMul s t) =
    stackOmega (fixedRho s) (fixedRho t) (fixedNu s) (fixedNu t) (fixedOmega s) (fixedOmega t) :=
  (fixedMul_data s t).2.2

end Stacking

/-- Interchange uses the explicit parity and scalar gauges. -/
theorem twistMul_comm {G : FiniteGrp.{0}} (s t : TwistOn G) :
    GaugeEquivalentOn (twistMul s t) (twistMul t s) := by
  apply (gaugeEquivalentOn_iff _ _).mpr
  refine ⟨typeSwapParity (fixedRho s) (fixedRho t),
    (fun g h => realSign (swapCorrection (fixedRho s) (fixedRho t) (fixedNu s) (fixedNu t) g h)),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [typeSwapParity]
  · intro g
    simp [swapCorrection, typeSwapScalar, typeSwapParity, fixedNu_one_left]
  · intro g
    simp [swapCorrection, typeSwapScalar, typeSwapParity, fixedNu_one_right]
  · simp only [fixedRho_mul, mul_comm]
  · rw [fixedNu_mul, fixedNu_mul]
    funext g h
    simp only [sumNu, parityMove, cross, typeSwapParity, map_mul, bwBit_mul]
    ring_nf
    simp [CharTwo.two_eq_zero]
  · rw [fixedOmega_mul, fixedOmega_mul, fixedNu_mul]
    exact (stackOmega_swap _ _ _ _ _ _ (fixedNu_cocycle s) (fixedNu_cocycle t)).symm

/-- Rebracketing has zero parity and the explicit associator scalar gauge. -/
theorem twistMul_assoc {G : FiniteGrp.{0}} (s t u : TwistOn G) :
    GaugeEquivalentOn (twistMul (twistMul s t) u) (twistMul s (twistMul t u)) := by
  apply (gaugeEquivalentOn_iff _ _).mpr
  refine ⟨(fun _ => 0), (fun g h => realSign
    (associatorCorrection (fixedRho s) (fixedRho t) (fixedRho u) (fixedNu u) g h)),
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    simp [associatorCorrection, typeAssociator, cross]
  · intro g
    simp [associatorCorrection, typeAssociator, cross]
  · simp only [fixedRho_mul, mul_assoc]
  · simp only [fixedNu_mul, fixedRho_mul]
    funext g h
    simp only [sumNu, parityMove, cross, MonoidHom.mul_apply, bwBit_mul]
    ring
  · simp only [fixedOmega_mul, fixedNu_mul, fixedRho_mul]
    exact (stackOmega_assoc _ _ _ _ _ _ _ _ _ (fixedNu_cocycle u)).symm

/-- Changing the first input produces the explicitly corrected product gauge. -/
theorem twistMul_congr_left {G : FiniteGrp.{0}} {s s' : TwistOn G}
    (hs : GaugeEquivalentOn s s') (t : TwistOn G) :
    GaugeEquivalentOn (twistMul s t) (twistMul s' t) := by
  obtain ⟨l, b, hl, hb₁, hb₂, hr, hv, ha⟩ := (gaugeEquivalentOn_iff _ _).mp hs
  apply (gaugeEquivalentOn_iff _ _).mpr
  refine ⟨l, (fun g h => b g h * realSign
    (gaugeLeftCorrection (fixedRho s) (fixedRho t) (fixedNu t) l g h)),
    hl, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    simp [gaugeLeftCorrection, cross, hb₁, fixedNu_one_left]
  · intro g
    simp [gaugeLeftCorrection, cross, hb₂, fixedNu_one_right]
  · simp only [fixedRho_mul, hr]
  · simp only [fixedNu_mul, hr, hv]
    funext g h
    simp only [sumNu, parityMove]
    ring
  · simp only [fixedOmega_mul, fixedNu_mul, hr, hv, ha]
    exact stackOmega_gauge_left _ _ _ _ _ _ _ _ (fixedNu_cocycle t)

/-- Gauge compatibility in both variables follows with the same fixed labels. -/
theorem twistMul_congr {G : FiniteGrp.{0}} {s s' t t' : TwistOn G}
    (hs : GaugeEquivalentOn s s') (ht : GaugeEquivalentOn t t') :
    GaugeEquivalentOn (twistMul s t) (twistMul s' t') :=
  gaugeEquivalentOn_trans (twistMul_congr_left hs t)
    (gaugeEquivalentOn_trans (twistMul_comm s' t)
      (gaugeEquivalentOn_trans (twistMul_congr_left ht s') (twistMul_comm t' s')))

/-- The quotient multiplication is the operation from the displayed cochains. -/
private def quotientMul (G : FiniteGrp.{0}) (x y : TwistClass G) : TwistClass G :=
  Quot.liftOn₂ x y (fun s t => twistClass (twistMul s t))
    (fun s _ _ ht => Quot.sound (twistMul_congr (gaugeEquivalentOn_refl s) ht))
    (fun _ _ t hs => Quot.sound (twistMul_congr hs (gaugeEquivalentOn_refl t)))

instance twistClassCommGroup (G : FiniteGrp.{0}) : CommGroup (TwistClass G) := by
  letI : Mul (TwistClass G) := ⟨quotientMul G⟩
  letI : One (TwistClass G) := ⟨twistClass (twistUnit G)⟩
  letI : Inv (TwistClass G) := ⟨fun x => twistClass (twistInv (Quot.out x))⟩
  have hassoc : ∀ a b c : TwistClass G, a * b * c = a * (b * c) := by
    intro a b c
    refine Quot.induction_on₃ a b c ?_
    intro s t u
    exact Quot.sound (twistMul_assoc s t u)
  have hunit : ∀ a : TwistClass G, a * 1 = a := by
    intro a
    refine Quot.induction_on a ?_
    intro s
    change twistClass (twistMul s (twistUnit G)) = twistClass s
    rw [twistMul_unit]
  have hinv : ∀ a : TwistClass G, a * a⁻¹ = 1 := by
    intro a
    change quotientMul G a (twistClass (twistInv (Quot.out a))) = twistClass (twistUnit G)
    conv_lhs => arg 2; rw [← Quot.out_eq a]
    change twistClass (twistMul (Quot.out a) (twistInv (Quot.out a))) = _
    rw [twistMul_inv]
  exact { Group.ofRightAxioms hassoc hunit hinv with
    mul_comm := by
      intro a b
      refine Quot.induction_on₂ a b ?_
      intro s t
      exact Quot.sound (twistMul_comm s t) }

theorem twistClassCommGroup_data {G : FiniteGrp.{0}} (s t : TwistOn G) :
    twistClass s * twistClass t = twistClass (twistMul s t) ∧
      (1 : TwistClass G) = twistClass (twistUnit G) ∧
      (twistClass s)⁻¹ = twistClass (twistInv s) := by
  refine ⟨rfl, rfl, ?_⟩
  apply inv_eq_of_mul_eq_one_right
  change twistClass (twistMul s (twistInv s)) = twistClass (twistUnit G)
  rw [twistMul_inv]

/-- The degree is induced by the unchanged degree of every fixed-label gauge. -/
def degree (G : FiniteGrp.{0}) : TwistClass G →* (G →* Multiplicative (ZMod 8)) where
  toFun := Quot.lift fixedRho (fun _ _ h => gaugeEquivalentOn_rho h)
  map_one' := rfl
  map_mul' := by
    intro a b
    refine Quot.induction_on₂ a b ?_
    exact fixedRho_mul

theorem degree_data {G : FiniteGrp.{0}} (s : TwistOn G) :
    degree G (twistClass s) = (s.property ▸ s.val.rho) := rfl
abbrev SHReal (G : FiniteGrp.{0}) := (degree G).ker

end RMod.BrundanEllis
