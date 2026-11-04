import RMod.BrundanEllis.StackingReferenceTripleEvaluation

/-! The chosen binary comparisons obey associativity at the local reference level for the scalar extracted from their actual triple routes. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace RMod.BrundanEllis.Stacking
open RMod.Classification
local notation "R" => reference.data.toWeaklyPointedSuperfusionData
local notation "hR" => referenceProperty.toWeaklyPointedSuperfusionLaws

/-- The actual binary comparison respects the two local associators when
the output scalar is the one read from the two parity-deletion routes.
The reference exchange equations are the only additional hypotheses. -/
theorem referenceTriple_coherence (b c d e : ZMod 8)
    (hl : ReferenceCommutor.LeftEquation b c e) (hr : ReferenceCommutor.RightEquation b d e)
    (A B C D E F : (R).Obj)
    (hB : InComponent R b B) (hC : InComponent R c C)
    (hD : InComponent R d D) (hE : InComponent R e E)
    (p₁₂ pL p₂₃ pR q₁₂ qL q₂₃ qR : ZMod 2)
    (hp : p₁₂ + pL = p₂₃ + pR) (hq : q₁₂ + qL = q₂₃ + qR) (ωs ωt ωu : ℝˣ)
    (hω : ωu.val = ωt.val * ωs.val * (-1 : ℝ) ^
      ((pL * q₁₂ + p₁₂ * q₁₂ + pL * qL +
        (pL + qL + ReferenceCommutor.degree (b + d) e) * ReferenceCommutor.degree b c +
        (ReferenceCommutor.rightDefect b d e + ReferenceCommutor.degree b c * ReferenceCommutor.degree d e)) +
        (pR * q₂₃ + p₂₃ * q₂₃ + pR * qR +
          (pR + qR + ReferenceCommutor.degree b (c + e)) * ReferenceCommutor.degree d e)).val) :
    (referenceTripleLeftData b c d e A B C D E F hB hC hD hE
      p₁₂ pL p₂₃ pR q₁₂ qL q₂₃ qR hp hq ωs ωt).hom =
    (referenceTripleRightData b c d e A B C D E F hB hC hD hE
      p₁₂ pL p₂₃ pR q₁₂ qL q₂₃ qR hp hq ωu).hom := by
  have hbits (x y : ZMod 2) : (x + y) + y = x := by
    ring_nf
    simp [CharTwo.two_eq_zero]
  have hh : (R).comp
      (referenceTripleLeftData b c d e A B C D E F hB hC hD hE
        p₁₂ pL p₂₃ pR q₁₂ qL q₂₃ qR hp hq ωs ωt).hom
      (referenceTripleTargetDeletionData A B C D E F p₂₃ pR q₂₃ qR).hom =
      (R).comp
        (referenceTripleRightData b c d e A B C D E F hB hC hD hE
          p₁₂ pL p₂₃ pR q₁₂ qL q₂₃ qR hp hq ωu).hom
        (referenceTripleTargetDeletionData A B C D E F p₂₃ pR q₂₃ qR).hom := by
    rw [referenceTripleLeft_deletion b c d e hl hr, referenceTripleRight_deletion, hω]
    simp only [mul_assoc, ← parity_power_add, hbits]
  have hi := referenceTripleTargetDeletionLaws A B C D E F p₂₃ pR q₂₃ qR
  have hc := congrArg (fun f => (R).comp f
    (referenceTripleTargetDeletionData A B C D E F p₂₃ pR q₂₃ qR).inv) hh
  simpa only [(hR).comp_assoc, hi.hom_inv, (hR).comp_id] using hc

end RMod.BrundanEllis.Stacking
