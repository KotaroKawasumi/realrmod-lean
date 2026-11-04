import RMod.Classification.Proofs.Decompositions

/-!
# Homogeneous sections and retractions at a simple object

A semisimple decomposition detects a nonzero matrix coefficient of the
given map. Graded Schur inverts that coefficient, and its inclusion or
projection supplies the desired homogeneous splitting. The result does
not require the simple object to be the tensor unit or to have type zero.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{u, v})

theorem homogeneous_simple_retraction {S V : C.data.Obj} (hS : C.data.IsSimple S) {a : ZMod 2}
    (f : C.data.Hom S V) (hf : C.data.IsHomogeneous a f) (hne : f ≠ C.data.zero) :
    ∃ g : C.data.Hom V S, C.data.comp f g = C.data.id S ∧ C.data.IsHomogeneous a g := by
  obtain ⟨n, T, hT, i, p, hi, hp, hd, ho, ht⟩ := C.laws.semisimple V
  have hex : ∃ j, C.data.comp f (p j) ≠ C.data.zero := by
    by_contra h
    apply hne
    apply hom_ext_of_projections C.laws i p ht
    intro j
    have hz : C.data.comp f (p j) = C.data.zero := by
      by_contra hj
      exact h ⟨j, hj⟩
    rw [hz, raw_zero_comp C.laws]
  obtain ⟨j, hj⟩ := hex
  have hfj := C.laws.comp_grade _ _ hf (hp j)
  rw [add_zero] at hfj
  obtain ⟨g, hfg, hgf⟩ := C.laws.graded_schur hS (hT j) (C.data.comp f (p j)) hfj hj
  have hg := homogeneous_inverse C.laws _ g hfg hgf hfj
  refine ⟨C.data.comp (p j) g, ?_, ?_⟩
  · rw [← C.laws.comp_assoc, hfg]
  · have h := C.laws.comp_grade _ _ (hp j) hg
    rw [zero_add] at h
    exact h

theorem homogeneous_simple_section {S V : C.data.Obj} (hS : C.data.IsSimple S) {a : ZMod 2}
    (f : C.data.Hom V S) (hf : C.data.IsHomogeneous a f) (hne : f ≠ C.data.zero) :
    ∃ g : C.data.Hom S V, C.data.comp g f = C.data.id S ∧ C.data.IsHomogeneous a g := by
  obtain ⟨n, T, hT, i, p, hi, hp, hd, ho, ht⟩ := C.laws.semisimple V
  have hex : ∃ j, C.data.comp (i j) f ≠ C.data.zero := by
    by_contra h
    apply hne
    apply hom_ext_of_inclusions C.laws i p ht
    intro j
    have hz : C.data.comp (i j) f = C.data.zero := by
      by_contra hj
      exact h ⟨j, hj⟩
    rw [hz, raw_comp_zero C.laws]
  obtain ⟨j, hj⟩ := hex
  have hfj := C.laws.comp_grade _ _ (hi j) hf
  rw [zero_add] at hfj
  obtain ⟨g, hfg, hgf⟩ := C.laws.graded_schur (hT j) hS (C.data.comp (i j) f) hfj hj
  have hg := homogeneous_inverse C.laws _ g hfg hgf hfj
  refine ⟨C.data.comp g (i j), ?_, ?_⟩
  · rw [C.laws.comp_assoc, hgf]
  · have h := C.laws.comp_grade _ _ hg (hi j)
    rw [add_zero] at h
    exact h

end RMod.Classification
