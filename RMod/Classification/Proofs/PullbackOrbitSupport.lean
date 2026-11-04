import RMod.Classification.Proofs.PullbackOrbits

/-!
# A pullback simple's support is exactly its homogeneous orbit label

An isomorphism cannot move a nonzero simple coordinate to a zero
coordinate. Conversely, simples in the same support have the same
intrinsic reference type, and the reference property supplies their
homogeneous isomorphism. This identifies the categorical orbit label
with the original group coordinate without an extra grading assumption.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C)
  (t : TwistData) (ht : TwistLaws t)

theorem pullback_sameOrbit_iff_support_eq (X Y : PullbackObj C t) (g h : t.group)
    (hX : ∀ k, k ≠ g → C.id (X k).val = C.zero)
    (hY : ∀ k, k ≠ h → C.id (Y k).val = C.zero)
    (hsX : C.IsSimple (X g).val) (hsY : C.IsSimple (Y h).val) :
    SameParityOrbit (twistedPullbackData C hC t ht).toWeaklyPointedSuperfusionData X Y ↔ g = h := by
  constructor
  · rintro ⟨a, f, p, hfp, _, _, _⟩
    by_contra he
    have hz := hom_eq_zero_of_target hC.toWeaklyPointedSuperfusionLaws (hY g he) (f g)
    have hi : C.comp (f g) (p g) = C.id (X g).val := congrFun hfp g
    rw [hz, raw_zero_comp hC.toWeaklyPointedSuperfusionLaws] at hi
    exact simple_id_ne_zero hC.toWeaklyPointedSuperfusionLaws hsX hi.symm
  · intro he
    subst h
    have htx := (InComponent.simple_iff hC hsX _).mp (X g).property
    have hty := (InComponent.simple_iff hC hsY _).mp (Y g).property
    obtain ⟨a, ha⟩ := (hC.type_detects_orbit _ _ _ hsX hsY htx).mp hty
    exact ⟨a, twistedPullback_supported_homogeneousIso C hC t ht g hX hY ha⟩

end RMod.Classification
