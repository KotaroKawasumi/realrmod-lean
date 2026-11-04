import RMod.Classification.Proofs.TwistedPullbackLaws

/-!
# The completed pullback and twist of an abstract reference category

Bundle the already specified data with their proved laws. Every category
operation and every proof depends on the supplied category and its
reference property, with no use of concrete data of the real model.
-/

set_option autoImplicit false

namespace RMod.Classification

noncomputable def twistedPullback (C : PiSuperfusionData.{0, 0})
    (hC : ReferenceProperty C) (t : Twist) : PiSuperfusion.{0, 0} where
  data := twistedPullbackData C hC t.data t.laws
  laws := twistedPullbackLaws C hC t.data t.laws

end RMod.Classification
