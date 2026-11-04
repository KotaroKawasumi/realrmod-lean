import RMod.Classification.Proofs.ParitySchur
import RMod.Classification.Proofs.PullbackSimples

/-!
# Even Schur for supported pullback objects

A nonzero endomorphism of a supported object is nonzero at its support.
Invert its even coordinate map in C and extend the inverse by zero.
Single-component Hom extensionality proves both inverse equations on the
whole family, before the convolution duality laws are assembled.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)

theorem twistedPullback_supported_even_schur (B : PullbackObj C t) (g : t.group)
    (hB : ∀ k, k ≠ g → C.id (B k).val = C.zero)
    (hs : ∀ f : C.Hom (B g).val (B g).val,
      C.IsHomogeneous 0 f → f ≠ C.zero → C.IsEvenIso f)
    (f : PullbackHom C t B B) (hf : ∀ k, C.IsHomogeneous 0 (f k))
    (hne : f ≠ (fun _ => C.zero)) : (twistedPullbackData C hC t ht).IsEvenIso f := by
  have hfg : f g ≠ C.zero := by
    intro he
    exact hne (hom_ext_of_supported_source C t g hC.toWeaklyPointedSuperfusionLaws hB f
      (fun _ => C.zero) he)
  obtain ⟨_, s₀, hs₀, hfs₀, hsf₀⟩ := hs (f g) (hf g) hfg
  let s : PullbackHom C t B B := singleComponentHom C t g s₀
  have hse : ∀ k, C.IsHomogeneous 0 (s k) :=
    singleComponentHom_grade C t g hC.toWeaklyPointedSuperfusionLaws s₀ hs₀
  have hfs : (fun k => C.comp (f k) (s k)) = (fun k => C.id (B k).val) := by
    apply hom_ext_of_supported_source C t g hC.toWeaklyPointedSuperfusionLaws hB
    change C.comp (f g) (singleComponentHom C t g s₀ g) = C.id (B g).val
    rw [singleComponentHom_at, hfs₀]
  have hsf : (fun k => C.comp (s k) (f k)) = (fun k => C.id (B k).val) := by
    apply hom_ext_of_supported_source C t g hC.toWeaklyPointedSuperfusionLaws hB
    change C.comp (singleComponentHom C t g s₀ g) (f g) = C.id (B g).val
    rw [singleComponentHom_at, hsf₀]
  exact ⟨hf, s, hse, hfs, hsf⟩

theorem twistedPullback_placed_even_schur (g : t.group) (S : C.Obj)
    (hS : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g)) S)
    (hs : ∀ f : C.Hom S S, C.IsHomogeneous 0 f → f ≠ C.zero → C.IsEvenIso f)
    (f : PullbackHom C t (placedObj C hC t g S hS) (placedObj C hC t g S hS))
    (hf : ∀ k, C.IsHomogeneous 0 (f k)) (hne : f ≠ (fun _ => C.zero)) :
    (twistedPullbackData C hC t ht).IsEvenIso f := by
  apply twistedPullback_supported_even_schur C hC t ht _ g _ _ f hf hne
  · intro k hk
    rw [placedObj_away C hC t g S hS k hk]
    exact pullbackZero_id C hC t k
  · dsimp only [placedObj]
    rw [if_pos (show g = g from rfl)]
    exact hs

end RMod.Classification
