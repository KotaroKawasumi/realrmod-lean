import RMod.Classification.Proofs.SingleComponentHom
import RMod.Classification.Proofs.ComponentPlacement
import RMod.Classification.Proofs.SimpleSplitting
import RMod.Classification.Instances.TwistedPullbackData

/-!
# Simple objects supported in one group component

A nonzero even monomorphism into such an object has a nonzero coordinate
at its support. Semisimplicity in C splits that coordinate; extension by
zero gives a section in the pullback, and monicity gives the other inverse
identity. Thus this argument uses no unproved fusion laws of the pullback.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)

theorem twistedPullback_supported_simple (B : PullbackObj C t) (g : t.group)
    (hB : ∀ k, k ≠ g → C.id (B k).val = C.zero) (hs : C.IsSimple (B g).val) :
    (twistedPullbackData C hC t ht).IsSimple B := by
  intro A f hf
  constructor
  · rintro ⟨_, s, _, _, hsf⟩ he
    apply simple_id_ne_zero hC.toWeaklyPointedSuperfusionLaws hs
    have hh := congrFun hsf g
    change C.comp (s g) (f g) = C.id (B g).val at hh
    have hz : f g = C.zero := congrFun he g
    rw [hz, raw_comp_zero hC.toWeaklyPointedSuperfusionLaws] at hh
    exact hh.symm
  · intro hne
    have hfg : f g ≠ C.zero := by
      intro he
      apply hne
      exact hom_ext_of_supported_target C t g hC.toWeaklyPointedSuperfusionLaws hB f
        (fun _ => C.zero) he
    obtain ⟨s₀, hs₀, hse⟩ := homogeneous_simple_section
      ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩ hs (f g) (hf.1 g) hfg
    let s : PullbackHom C t B A := singleComponentHom C t g s₀
    have hse' : ∀ k, C.IsHomogeneous 0 (s k) :=
      singleComponentHom_grade C t g hC.toWeaklyPointedSuperfusionLaws s₀ hse
    have hsf : (fun k => C.comp (s k) (f k)) = (fun k => C.id (B k).val) := by
      apply hom_ext_of_supported_source C t g hC.toWeaklyPointedSuperfusionLaws hB
      change C.comp (singleComponentHom C t g s₀ g) (f g) = C.id (B g).val
      rw [singleComponentHom_at, hs₀]
    have hfs : (fun k => C.comp (f k) (s k)) = (fun k => C.id (A k).val) := by
      apply hf.2 A
      · intro k
        exact comp_even hC.toWeaklyPointedSuperfusionLaws (hf.1 k) (hse' k)
      · exact fun k => hC.id_even (A k).val
      · funext k
        change C.comp (C.comp (f k) (s k)) (f k) = C.comp (C.id (A k).val) (f k)
        rw [hC.comp_assoc, congrFun hsf k, hC.comp_id, hC.id_comp]
    exact ⟨hf.1, s, hse', hfs, hsf⟩

theorem twistedPullback_placed_simple (g : t.group) (S : C.Obj)
    (hS : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g)) S)
    (hs : C.IsSimple S) :
    (twistedPullbackData C hC t ht).IsSimple (placedObj C hC t g S hS) := by
  apply twistedPullback_supported_simple C hC t ht _ g
  · intro k hk
    rw [placedObj_away C hC t g S hS k hk]
    exact pullbackZero_id C hC t k
  · rw [placedObj_at]
    exact hs

end RMod.Classification
