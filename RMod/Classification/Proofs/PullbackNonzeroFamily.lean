import RMod.Classification.Abstract.Pullback
import RMod.Classification.Proofs.Components

/-!
# A pullback family nonzero in every degree

Realization of every intrinsic type supplies a simple in each required
component. Only existence is needed to test coherence on nonzero maps;
this lemma makes no extra choice in the constructed tensor data.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem pullback_exists_nonzero_family (C : PiSuperfusionData.{0, 0})
    (hC : ReferenceProperty C) (t : TwistData) :
    ∃ X : PullbackObj C t, ∀ g : t.group, C.id (X g).val ≠ C.zero := by
  classical
  choose S hs ht using fun g : t.group => hC.realizes_type (Multiplicative.toAdd (t.rho g))
  refine ⟨fun g => ⟨S g, InComponent.of_simple hC (hs g) (ht g)⟩, ?_⟩
  intro g
  exact simple_id_ne_zero hC.toWeaklyPointedSuperfusionLaws (hs g)

end RMod.Classification
