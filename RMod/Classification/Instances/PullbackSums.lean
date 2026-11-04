import RMod.Classification.Instances.TwistedPullbackData

/-!
# Chosen biproduct data in the pullback

Take C's chosen finite sum in each group coordinate. Closure of each
intrinsic type component under finite sums ensures that this is again
a pullback object. Inclusions and projections are the original coordinate
maps, and their laws are proved separately.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

noncomputable def pullbackSumObj {n : ℕ} (S : Fin n → PullbackObj C t) : PullbackObj C t := fun g =>
  ⟨((finiteSumsData C hC.toWeaklyPointedSuperfusionLaws).sum (fun i => (S i g).val)).object,
    finiteSums_inComponent C hC (fun i => (S i g).val) (Multiplicative.toAdd (t.rho g))
      (fun i => (S i g).property)⟩

noncomputable def pullbackSumData (ht : TwistLaws t) {n : ℕ} (S : Fin n → PullbackObj C t) :
    BiproductData (twistedPullbackData C hC t ht) S where
  object := pullbackSumObj C hC t S
  inclusion i g := ((finiteSumsData C hC.toWeaklyPointedSuperfusionLaws).sum
    (fun j => (S j g).val)).inclusion i
  projection i g := ((finiteSumsData C hC.toWeaklyPointedSuperfusionLaws).sum
    (fun j => (S j g).val)).projection i

end RMod.Classification
