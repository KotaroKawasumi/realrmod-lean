import RMod.Classification.Proofs.IsoCalculus

/-!
# A normalized scalar equation is the tensorator associativity diagram

Cancel the right normalizer and the two tensorator inverse pairs. This
recovers the associativity square with the scalar multiplying R⁻¹ L.
The statement retains the equality map between the two normal forms.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

variable {C : WeaklyPointedSuperfusionData.{u, v}} (hC : WeaklyPointedSuperfusionLaws C)

include hC

theorem normalized_scalar_transport {L₀ R₀ X Y Q Q' : C.Obj}
    (tL : IsoData C L₀ X) (tR : IsoData C R₀ Y) (L : IsoData C L₀ Q) (R : IsoData C R₀ Q')
    (e : IsoData C Q Q') (α : C.Hom X Y) (r : ℝˣ)
    (htL : IsoLaws C tL) (htR : IsoLaws C tR) (hR : IsoLaws C R)
    (h : C.comp (C.comp α tR.inv) R.hom =
      C.smul (r : ℝ) (C.comp (C.comp tL.inv L.hom) e.hom)) :
    C.comp tL.hom α = C.comp ((L.trans C (e.trans C (R.symm C))).scale C r).hom tR.hom := by
  have hh := congrArg (fun f => C.comp tL.hom (C.comp f (C.comp R.inv tR.hom))) h
  simp only [hC.comp_smul, hC.smul_comp, hC.comp_assoc,
    ← hC.comp_assoc R.hom R.inv, hR.hom_inv, hC.id_comp,
    htR.inv_hom,
    ← hC.comp_assoc tL.hom tL.inv, htL.hom_inv, hC.comp_id] at hh
  change C.comp tL.hom α = C.comp (C.smul (r : ℝ)
    (C.comp L.hom (C.comp e.hom R.inv))) tR.hom
  simpa only [hC.smul_comp, hC.comp_assoc, hC.id_comp] using hh

end RMod.Classification
