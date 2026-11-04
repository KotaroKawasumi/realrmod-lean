import RMod.BrundanEllis.StackingDeletionCorrection
import RMod.BrundanEllis.StackingCrossingTwist

/-! A valid auxiliary twist with the explicit deletion-correction formula.
It is gauge equivalent to the prescribed product and its pullback is
monoidally superequivalent to that product's pullback. Identifying it with
the actual completed diagonal remains a separate categorical obligation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis.Stacking
open Superfusion
variable {G : FiniteGrp.{0}}

/-- The zero-parity gauge realizes the explicit algebraic deletion convention. -/
def comparisonGaugeData (s t : TwistOn G) : GaugeData (twistMul s t).val.toTwistData where
  targetGroup := G
  phi := (twistMul s t).property.symm ▸ MulEquiv.refl G
  lam := fun _ => 0
  beta := (twistMul s t).property.symm ▸
    (fun g h : G => realSign (comparisonGaugeExponent (fixedRho s) (fixedRho t) (fixedNu s) (fixedNu t) g h))

/-- The entire comparison exponent vanishes whenever an input label is the unit. -/
def comparisonGauge (s t : TwistOn G) : Gauge (twistMul s t).val.toTwistData :=
  ⟨comparisonGaugeData s t, rfl,
    by
      rcases s with ⟨s, hs⟩
      subst G
      intro g
      exact congrArg realSign ((comparisonGaugeExponent_normalized _ _ _ _).1 g),
    by
      rcases s with ⟨s, hs⟩
      subst G
      intro g
      exact congrArg realSign ((comparisonGaugeExponent_normalized _ _ _ _).2 g)⟩

/-- Construct the auxiliary twist with the algebraic deletion correction. -/
def comparisonTwist (s t : TwistOn G) : TwistOn G :=
  ⟨gaugeTransform (twistMul s t).val (comparisonGauge s t), by with_unfolding_all rfl⟩

/-- All three cochains are fixed by the explicit deletion-correction formula. -/
theorem comparisonTwist_data (s t : TwistOn G) :
    fixedRho (comparisonTwist s t) = fixedRho s * fixedRho t ∧
    fixedNu (comparisonTwist s t) = sumNu (fixedRho s) (fixedRho t) (fixedNu s) (fixedNu t) ∧
    fixedOmega (comparisonTwist s t) = fun g h k =>
      fixedOmega s g h k * fixedOmega t g h k *
        realSign (deletionCorrection (fixedRho s) (fixedRho t) (fixedNu s) (fixedNu t) g h k) := by
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
      (fun g h => realSign (comparisonGaugeExponent r q v w g h)) = _
    have hv : ∀ g h k, d₂ v g h k = 0 := by
      simpa only [d₂, CharTwo.sub_eq_add] using s6
    have hw : ∀ g h k, d₂ w g h k = 0 := by
      simpa only [d₂, CharTwo.sub_eq_add] using t6
    convert deletionOmega_scalarMove r q v w hv hw a b using 1
    · congr 1
      change (fun g h k => a g h k * b g h k * realSign
        (cupOne w v g h k + cupOne (cross r q) (fun i j => v i j + w i j) g h k +
          bwPrimitive (r g) * bwBit (q h) * bwBit (q k) +
            bwBit (r g) * (bwBit (r h) * bwBit (q h)) * bwBit (q k))) = _
      funext g h k
      simp only [stackOmega, correction, typeCorrection, add_assoc]
    · rfl

/-- The auxiliary convention is preserved by restriction of group labels. -/
theorem baseChange_comparisonTwist {H : FiniteGrp.{0}} (f : H →* G) (s t : TwistOn G) :
    baseChange f (comparisonTwist s t) = comparisonTwist (baseChange f s) (baseChange f t) := by
  apply fixed_ext
  · simp only [(baseChange_data _ _).1, (comparisonTwist_data _ _).1]
    ext g
    rfl
  · simp only [(baseChange_data _ _).2.1, (comparisonTwist_data _ _).2.1,
      (baseChange_data _ _).1]
    rfl
  · simp only [(baseChange_data _ _).2.2, (comparisonTwist_data _ _).2.2,
      (baseChange_data _ _).2.1, (baseChange_data _ _).1]
    funext g h k
    simp [deletionCorrection, cupOne, sumNu, cross, map_mul]

/-- This gauge retains the common group label. -/
theorem comparisonTwist_gauge (s t : TwistOn G) :
    GaugeEquivalentOn (twistMul s t) (comparisonTwist s t) := by
  refine ⟨comparisonGauge s t, (twistMul s t).property.symm, ?_, rfl⟩
  rcases s with ⟨s, hs⟩
  subst G
  rfl

/-- Its pullback is equivalent to the prescribed product. Identifying it with the completed diagonal remains a separate theorem. -/
theorem comparisonTwist_pullback (s t : TwistOn G) :
    MonoidallySuperequivalent (pullback (comparisonTwist s t).val)
      (pullback (twistMul s t).val) := by
  apply (equivalence_iff_gauge realRMod real_isBrauerWallReference _ _).mpr
  obtain ⟨d, _, _, hd⟩ := gaugeEquivalentOn_symm (comparisonTwist_gauge s t)
  exact ⟨d, hd⟩

end RMod.BrundanEllis.Stacking
