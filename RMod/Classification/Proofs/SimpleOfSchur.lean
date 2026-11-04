import RMod.Classification.Proofs.SimpleDecomposition
import RMod.Classification.Proofs.SimpleIso
import RMod.Classification.Proofs.DualSchur
import RMod.Classification.Proofs.DualNonzero

/-!
# Recovering simplicity from the even division property

In a semisimple category, the projector onto any simple constituent is
nonzero. If every nonzero even endomorphism is invertible, this idempotent
must be the identity, so its inclusion is an even isomorphism. Applying
this criterion to dual mates proves simplicity of both dual objects.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{0, 0})

theorem simple_of_even_schur {Y : C.data.Obj} (hY : C.data.id Y ≠ C.data.zero)
    (hSchur : ∀ f : C.data.Hom Y Y, C.data.IsHomogeneous 0 f → f ≠ C.data.zero →
      C.data.IsEvenIso f) : C.data.IsSimple Y := by
  let d := simpleDecomposition C Y
  let k : Fin d.data.size := ⟨0, d.size_pos hY⟩
  let i := d.data.decomposition.inclusion k
  let p := d.data.decomposition.projection k
  have hip : C.data.comp i p = C.data.id (d.data.summand k) := d.laws.decomposition.diagonal k
  let e := C.data.comp p i
  have hne : e ≠ C.data.zero := by
    intro hz
    have hh : C.data.comp (C.data.comp i e) p = C.data.id (d.data.summand k) := by
      dsimp only [e]
      rw [← C.laws.comp_assoc i p i, hip, C.laws.id_comp, hip]
    rw [hz, raw_comp_zero C.laws, raw_zero_comp C.laws] at hh
    exact simple_id_ne_zero C.laws (d.laws.simple k) hh.symm
  have hg : C.data.IsHomogeneous 0 e := by
    have hh := C.laws.comp_grade p i (d.laws.decomposition.projection_even k)
      (d.laws.decomposition.inclusion_even k)
    rw [zero_add] at hh
    exact hh
  obtain ⟨_, g, _, heg, _⟩ := hSchur e hg hne
  have hee : C.data.comp e e = e := by
    change C.data.comp (C.data.comp p i) (C.data.comp p i) = C.data.comp p i
    rw [C.laws.comp_assoc, ← C.laws.comp_assoc i p i, hip, C.laws.id_comp]
  have he : e = C.data.id Y := by
    calc
      e = C.data.comp e (C.data.id Y) := (C.laws.comp_id e).symm
      _ = C.data.comp e (C.data.comp e g) := by rw [heg]
      _ = C.data.comp e g := by rw [← C.laws.comp_assoc, hee]
      _ = C.data.id Y := heg
  exact simple_of_evenIso C ⟨i, p⟩
    { hom_inv := hip, inv_hom := he,
      hom_even := d.laws.decomposition.inclusion_even k,
      inv_even := d.laws.decomposition.projection_even k } (d.laws.simple k)

namespace DualPairing

variable {C} {X Y : C.data.Obj} (q : DualPairing C X Y)

include q

theorem right_simple (hX : C.data.IsSimple X) : C.data.IsSimple Y :=
  simple_of_even_schur C (q.right_id_ne_zero (simple_id_ne_zero C.laws hX))
    (q.right_even_schur hX)

theorem left_simple (hY : C.data.IsSimple Y) : C.data.IsSimple X :=
  simple_of_even_schur C (q.left_id_ne_zero (simple_id_ne_zero C.laws hY))
    (q.left_even_schur hY)

end DualPairing
end RMod.Classification
