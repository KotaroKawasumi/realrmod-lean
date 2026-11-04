import RMod.BrundanEllis.StackingReferenceCrossingGauge
import RMod.BrundanEllis.StackingBaseChange
import RMod.BrundanEllis.StackingModelBridge

/-! The cochain gauge needed by the reversed exterior comparison is an actual
normalized gauge. Its target twist has the crossing-oriented scalar cochain,
and its pullback is monoidally superequivalent to the prescribed product. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis.Stacking
open Superfusion
variable {G : FiniteGrp.{0}}

/-- The zero-parity gauge moves the quadratic primitive to the final label. -/
def crossingGaugeData (s t : TwistOn G) : GaugeData (twistMul s t).val.toTwistData where
  targetGroup := G
  phi := (twistMul s t).property.symm ▸ MulEquiv.refl G
  lam := fun _ => 0
  beta := (twistMul s t).property.symm ▸
    (fun g h : G => realSign (crossingPrimitive (fixedRho s) (fixedRho t) g h))

/-- Normalization follows from the vanishing of the quadratic primitive at 1. -/
def crossingGauge (s t : TwistOn G) : Gauge (twistMul s t).val.toTwistData :=
  ⟨crossingGaugeData s t, rfl,
    by
      rcases s with ⟨s, hs⟩
      subst G
      intro g
      exact congrArg realSign ((crossingPrimitive_normalized _ _).1 g),
    by
      rcases s with ⟨s, hs⟩
      subst G
      intro g
      exact congrArg realSign ((crossingPrimitive_normalized _ _).2 g)⟩

/-- The auxiliary product is constructed by the already verified gauge move. -/
def crossingTwist (s t : TwistOn G) : TwistOn G :=
  ⟨gaugeTransform (twistMul s t).val (crossingGauge s t), by with_unfolding_all rfl⟩

/-- All three cochains are fixed; the scalar is the crossing-oriented formula. -/
theorem crossingTwist_data (s t : TwistOn G) :
    fixedRho (crossingTwist s t) = fixedRho s * fixedRho t ∧
    fixedNu (crossingTwist s t) = sumNu (fixedRho s) (fixedRho t) (fixedNu s) (fixedNu t) ∧
    fixedOmega (crossingTwist s t) = fun g h k =>
      fixedOmega s g h k * fixedOmega t g h k *
        realSign (crossingCorrection (fixedRho s) (fixedRho t) (fixedNu s) (fixedNu t) g h k) := by
  rcases s with ⟨s, hs⟩
  subst G
  rcases t with ⟨t, ht⟩
  rcases s with ⟨⟨S, r, v, a⟩, s1, s2, s3, s4, s5, s6, s7⟩
  rcases t with ⟨⟨T, q, w, b⟩, t1, t2, t3, t4, t5, t6, t7⟩
  change T = S at ht
  subst T
  constructor
  · rfl
  constructor
  · change parityMove (sumNu r q v w) (fun _ => 0) = sumNu r q v w
    funext g h
    simp only [parityMove, add_zero]
  · change scalarMove (sumNu r q v w) _ (fun _ => 0)
      (fun g h => realSign (crossingPrimitive r q g h)) = _
    convert crossingOmega_scalarMove r q v w a b using 1
    · congr 1
      change (fun g h k => a g h k * b g h k * realSign
        (cupOne w v g h k + cupOne (cross r q) (fun i j => v i j + w i j) g h k +
          bwPrimitive (r g) * bwBit (q h) * bwBit (q k) +
            bwBit (r g) * (bwBit (r h) * bwBit (q h)) * bwBit (q k))) = _
      funext g h k
      simp only [stackOmega, correction, typeCorrection, add_assoc]
    · rfl

/-- Restriction of group labels also preserves the crossing convention. -/
theorem baseChange_crossingTwist {H : FiniteGrp.{0}} (f : H →* G) (s t : TwistOn G) :
    baseChange f (crossingTwist s t) = crossingTwist (baseChange f s) (baseChange f t) := by
  apply fixed_ext
  · simp only [(baseChange_data _ _).1, (crossingTwist_data _ _).1]
    ext g
    rfl
  · simp only [(baseChange_data _ _).2.1, (crossingTwist_data _ _).2.1,
      (baseChange_data _ _).1]
    rfl
  · simp only [(baseChange_data _ _).2.2, (crossingTwist_data _ _).2.2,
      (baseChange_data _ _).2.1, (baseChange_data _ _).1]
    funext g h k
    simp [crossingCorrection, cupOne, cross, map_mul]

/-- This gauge retains the common group label. -/
theorem crossingTwist_gauge (s t : TwistOn G) :
    GaugeEquivalentOn (twistMul s t) (crossingTwist s t) := by
  refine ⟨crossingGauge s t, (twistMul s t).property.symm, ?_, rfl⟩
  rcases s with ⟨s, hs⟩
  subst G
  rfl

/-- Categorical use of the crossing convention returns to the fixed public cochains. -/
theorem crossingTwist_pullback (s t : TwistOn G) :
    MonoidallySuperequivalent (pullback (crossingTwist s t).val)
      (pullback (twistMul s t).val) := by
  apply (equivalence_iff_gauge realRMod real_isBrauerWallReference _ _).mpr
  obtain ⟨d, _, _, hd⟩ := gaugeEquivalentOn_symm (crossingTwist_gauge s t)
  exact ⟨d, hd⟩

end RMod.BrundanEllis.Stacking
