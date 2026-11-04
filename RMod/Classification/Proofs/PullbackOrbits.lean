import RMod.Classification.Proofs.PullbackSimpleSupport

/-!
# The finite homogeneous orbits of pullback simples

The reference property realizes every intrinsic type and identifies equal
types with homogeneous isomorphism classes. Choose one simple in each
group degree. Every pullback simple is supported in one degree and is
homogeneously isomorphic to the chosen representative there.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)

theorem twistedPullback_supported_homogeneousIso {X Y : PullbackObj C t} (g : t.group)
    (hX : ∀ k, k ≠ g → C.id (X k).val = C.zero)
    (hY : ∀ k, k ≠ g → C.id (Y k).val = C.zero) {a : ZMod 2}
    (he : C.HasHomogeneousIso a (X g).val (Y g).val) :
    (twistedPullbackData C hC t ht).HasHomogeneousIso a X Y := by
  obtain ⟨f, p, hfp, hpf, hf, hp⟩ := he
  refine ⟨singleComponentHom C t g f, singleComponentHom C t g p, ?_, ?_,
    singleComponentHom_grade C t g hC.toWeaklyPointedSuperfusionLaws f hf,
    singleComponentHom_grade C t g hC.toWeaklyPointedSuperfusionLaws p hp⟩
  · apply hom_ext_of_supported_source C t g hC.toWeaklyPointedSuperfusionLaws hX
    change C.comp (singleComponentHom C t g f g) (singleComponentHom C t g p g) = C.id (X g).val
    simp only [singleComponentHom_at, hfp]
  · apply hom_ext_of_supported_source C t g hC.toWeaklyPointedSuperfusionLaws hY
    change C.comp (singleComponentHom C t g p g) (singleComponentHom C t g f g) = C.id (Y g).val
    simp only [singleComponentHom_at, hpf]

theorem twistedPullback_finite_simple_representatives :
    ∃ (n : ℕ) (S : Fin n → (twistedPullbackData C hC t ht).Obj),
      (∀ j, (twistedPullbackData C hC t ht).IsSimple (S j)) ∧
      ∀ X, (twistedPullbackData C hC t ht).IsSimple X →
        ∃ (j : Fin n) (a : ZMod 2), (twistedPullbackData C hC t ht).HasHomogeneousIso a X (S j) := by
  classical
  choose S hs hr using fun g : t.group => hC.realizes_type (Multiplicative.toAdd (t.rho g))
  let hc g := InComponent.of_simple hC (hs g) (hr g)
  let T g := placedObj C hC t g (S g) (hc g)
  refine ⟨Nat.card t.group, fun j => T (groupEnumeration t j), ?_, ?_⟩
  · intro j
    exact twistedPullback_placed_simple C hC t ht _ _ _ (hs (groupEnumeration t j))
  · intro X hX
    obtain ⟨g, hx, hsx⟩ := twistedPullback_simple_support C hC t ht X hX
    have hy : ∀ k, k ≠ g → C.id (T g k).val = C.zero := by
      intro k hk
      change C.id (placedObj C hC t g (S g) (hc g) k).val = C.zero
      rw [placedObj_away C hC t g (S g) (hc g) k hk]
      exact pullbackZero_id C hC t k
    have hsy : C.IsSimple (T g g).val := by
      change C.IsSimple (placedObj C hC t g (S g) (hc g) g).val
      rw [placedObj_at]
      exact hs g
    have htx := (InComponent.simple_iff hC hsx _).mp (X g).property
    have hty := (InComponent.simple_iff hC hsy _).mp (T g g).property
    obtain ⟨a, he⟩ := (hC.type_detects_orbit _ _ _ hsx hsy htx).mp hty
    refine ⟨(groupEnumeration t).symm g, a, ?_⟩
    simpa only [Equiv.apply_symm_apply] using
      twistedPullback_supported_homogeneousIso C hC t ht g hx hy he

end RMod.Classification
