import RMod.BrundanEllis.StackingBaseChange
import RMod.BrundanEllis.StackingModelBridge
import RMod.Classification.Instances.PullbackEvaluation
import RMod.Hierarchy.Bridge.Superfunctors

/-! Restrict the coordinate family along a group homomorphism. This is
an enriched functor before imposing any support condition; monoidal
compatibility will require support on the image of an injective map. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000
namespace RMod.Classification
variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (f : t.data.group →* s.data.group) (hρ : ∀ g, t.data.rho g = s.data.rho (f g))

/-- Restriction changes the label and retains the reference object and map. -/
def coordinateRestrictionData : SuperfunctorData
    (twistedPullback C hC s).data.toWeaklyPointedSuperfusionData
    (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData where
  obj X g := ⟨(X (f g)).val, by
    rw [hρ]
    exact (X (f g)).property⟩
  map u g := u (f g)

/-- Every enriched functor law is inherited pointwise. -/
theorem coordinateRestrictionLaws : SuperfunctorLaws
    (twistedPullback C hC s).data.toWeaklyPointedSuperfusionData
    (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData
    (coordinateRestrictionData C hC s t f hρ) where
  map_id _ := rfl
  map_comp _ _ := rfl
  map_zero _ _ := rfl
  map_add _ _ := rfl
  map_smul _ _ := rfl
  map_grade _ hu := fun g => hu (f g)

def coordinateRestriction : Superfunctor
    (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (twistedPullback C hC t).toWeaklyPointedSuperfusion :=
  ⟨coordinateRestrictionData C hC s t f hρ, coordinateRestrictionLaws C hC s t f hρ⟩
end RMod.Classification

namespace RMod.BrundanEllis.Stacking
/-- On the public pullback models, reindexing is the same coordinate restriction. -/
def pullbackReindex (s : Twist) {H : FiniteGrp.{0}} (f : H →* s.group) :
    SuperFunctor (pullback s) (pullback (reindexTwist s f).val) := by
  with_unfolding_all
    exact RMod.StatementLegacy.StatementBridge.fromFunctor
      (RMod.Legacy.Hierarchy.ofOldSuperfunctor
        (RMod.Classification.coordinateRestriction reference.data referenceProperty
          (oldTwist s) (oldTwist (reindexTwist s f).val) f (fun _ => rfl)))

end RMod.BrundanEllis.Stacking
