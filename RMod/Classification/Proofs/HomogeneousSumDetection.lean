import RMod.Classification.Abstract.HomogeneousSums
import RMod.Classification.Proofs.Decompositions

/-!
# Detecting nonzero maps through split inclusions and homogeneous sums

A left inverse prevents postcomposition from killing a nonzero map.
The total matrix identity for a homogeneous sum ensures that some
projection detects every nonzero map into its vertex. These statements
do not require the component maps to be even.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{u, v})

theorem comp_ne_zero_of_left_inverse {X Y Z : C.data.Obj}
    (f : C.data.Hom X Y) (j : C.data.Hom Y Z) (p : C.data.Hom Z Y)
    (hjp : C.data.comp j p = C.data.id Y) (hf : f ≠ C.data.zero) : C.data.comp f j ≠ C.data.zero := by
  intro hz
  apply hf
  calc
    f = C.data.comp (C.data.comp f j) p := by rw [C.laws.comp_assoc, hjp, C.laws.comp_id]
    _ = C.data.zero := by rw [hz, raw_zero_comp C.laws]

theorem HomogeneousSum.exists_nonzero_projection {S A X : C.data.Obj} {n : ℕ}
    (d : HomogeneousSum C.data S A n) (f : C.data.Hom X A) (hf : f ≠ C.data.zero) :
    ∃ i, C.data.comp f (d.data.projection i) ≠ C.data.zero := by
  by_contra h
  apply hf
  apply hom_ext_of_projections C.laws d.data.inclusion d.data.projection d.laws.total
  intro i
  have hz : C.data.comp f (d.data.projection i) = C.data.zero := by
    by_contra hi
    exact h ⟨i, hi⟩
  rw [hz, raw_zero_comp C.laws]

end RMod.Classification
