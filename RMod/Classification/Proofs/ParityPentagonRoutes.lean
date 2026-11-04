import RMod.Classification.Instances.ParityPentagonRoutes
import RMod.Classification.Proofs.Normalizers

/-!
# Even inverse laws of both parity pentagon routes

The two sides are genuine even isomorphisms with the same endpoints.
These elementary laws do not assert their signed equality: that equation
is the separate universal parity-word obligation.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiLaws

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C) {p : PiData C} (hp : PiLaws C p)

include hC hp

theorem parityPentagonThree_evenIso (W X Y Z : C.Obj) (a b c d e f q r s t : ZMod 2)
    (h₁ : a + b = c + d) (h₂ : c + f = e + q) (h₅ : d + t = f + s) :
    EvenIsoLaws C (p.parityPentagonThree W X Y Z a b c d e f q r s t h₁ h₂ h₅) := by
  have hA := ((hp.localAssociator_evenIso hC W X Y a b c d h₁ 1).tensor hC
    (EvenIsoLaws.refl hC Z)).tensor hC (EvenIsoLaws.refl hC (p.factor t))
  have hB := hp.localAssociator_evenIso hC W (C.tensorObj (C.tensorObj X Y) (p.factor c)) Z
    d t f s h₅ 1
  have hD := ((EvenIsoLaws.refl hC W).tensor hC
    (hp.localAssociator_evenIso hC X Y Z c f e q h₂ 1)).tensor hC (EvenIsoLaws.refl hC (p.factor s))
  exact (hA.trans hC hB).trans hC hD

theorem parityPentagonTwo_evenIso (W X Y Z : C.Obj) (a b c d e f q r s t : ZMod 2)
    (h₃ : a + r = q + s) (h₄ : b + t = e + r) :
    EvenIsoLaws C (p.parityPentagonTwo W X Y Z a b c d e f q r s t h₃ h₄) := by
  exact (hp.localAssociator_evenIso hC (C.tensorObj (C.tensorObj W X) (p.factor a)) Y Z
    b t e r h₄ 1).trans hC
    (hp.localAssociator_evenIso hC W X (C.tensorObj (C.tensorObj Y Z) (p.factor e)) a r q s h₃ 1)

end RMod.Classification.PiLaws
