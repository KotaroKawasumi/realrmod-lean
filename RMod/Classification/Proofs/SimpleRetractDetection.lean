import RMod.Classification.Instances.SimpleRetract
import RMod.Classification.Proofs.SimpleDecomposition
import RMod.Classification.Proofs.SimpleSplitting

/-!
# Detecting a simple retract inside an even idempotent

A nonzero idempotent acts nontrivially on some simple constituent.
Graded Schur supplies a retraction of that nonzero even inclusion.
Composing the retraction once more with the idempotent makes both maps
fixed by it, while retaining their inverse identity.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

attribute [local implicit_reducible] CategoryTheory.End

theorem exists_simpleRetract_under_idempotent (C : WeaklyPointedSuperfusion.{0, 0})
    (X : LinearCategory C) (e : End X) (he : C.data.IsHomogeneous 0 e)
    (hee : e ≫ e = e) (hne : e ≠ 0) :
    ∃ d : SimpleRetract C X,
      C.data.comp d.data.inclusion e = d.data.inclusion ∧
        C.data.comp e d.data.projection = d.data.projection := by
  change C.data.comp e e = e at hee
  change e ≠ C.data.zero at hne
  let d := simpleDecomposition C X
  have hex : ∃ k, C.data.comp (d.data.decomposition.inclusion k) e ≠ C.data.zero := by
    by_contra h
    apply hne
    apply hom_ext_of_inclusions C.laws d.data.decomposition.inclusion d.data.decomposition.projection
      d.laws.decomposition.total
    intro k
    have hk : C.data.comp (d.data.decomposition.inclusion k) e = C.data.zero := by
      by_contra hk
      exact h ⟨k, hk⟩
    rw [hk, raw_comp_zero C.laws]
  obtain ⟨k, hk⟩ := hex
  let j := C.data.comp (d.data.decomposition.inclusion k) e
  have hj : C.data.IsHomogeneous 0 j := by
    have h := C.laws.comp_grade _ _ (d.laws.decomposition.inclusion_even k) he
    simp only [zero_add] at h
    exact h
  obtain ⟨r, hjr, hr⟩ := homogeneous_simple_retraction C (d.laws.simple k) j hj hk
  have hje : C.data.comp j e = j := by
    change C.data.comp (C.data.comp (d.data.decomposition.inclusion k) e) e =
      C.data.comp (d.data.decomposition.inclusion k) e
    rw [C.laws.comp_assoc, hee]
  let s := C.data.comp e r
  have hjs : C.data.comp j s = C.data.id (d.data.summand k) := by
    change C.data.comp j (C.data.comp e r) = _
    rw [← C.laws.comp_assoc, hje, hjr]
  have hs : C.data.IsHomogeneous 0 s := by
    have h := C.laws.comp_grade _ _ he hr
    simp only [zero_add] at h
    exact h
  refine ⟨⟨⟨⟨d.data.summand k⟩, j, s⟩, ⟨⟨d.laws.simple k⟩, hjs, hj, hs⟩⟩, hje, ?_⟩
  change C.data.comp e (C.data.comp e r) = C.data.comp e r
  rw [← C.laws.comp_assoc, hee]

end RMod.Classification
