import RMod.Classification.Abstract.HomogeneousSpan
import RMod.Classification.Proofs.HomogeneousSumDetection
import RMod.Classification.Proofs.HomogeneousSums
import RMod.Classification.Proofs.SimpleDecomposition

/-!
# Homogeneous spans are intrinsic simple-orbit components

A nonzero homogeneous map from a simple to an object in a homogeneous
span is detected by one generator projection. Graded Schur then puts
that simple in the generator's parity orbit. Conversely, a simple
decomposition in a single orbit supplies a homogeneous sum presentation.
Thus membership is independent of the chosen decomposition.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{0, 0}) {S X Y : C.data.Obj}

theorem sameParityOrbit_of_nonzero_to_span (hS : C.data.IsSimple S) (hY : C.data.IsSimple Y)
    (hX : InHomogeneousSpan C S X) {a : ZMod 2} (f : C.data.Hom Y X)
    (hf : C.data.IsHomogeneous a f) (hne : f ≠ C.data.zero) : SameParityOrbit C.data Y S := by
  obtain ⟨n, ⟨d⟩⟩ := hX
  obtain ⟨i, hi⟩ := d.exists_nonzero_projection C f hne
  exact ⟨a + d.data.parity i, homogeneous_schur C.laws hY hS
    (C.data.comp f (d.data.projection i)) (C.laws.comp_grade _ _ hf (d.laws.projection_grade i)) hi⟩

theorem inHomogeneousSpan_iff_simple_decomposition (hS : C.data.IsSimple S)
    {n : ℕ} {V : Fin n → C.data.Obj} (d : Decomposition C X V)
    (hV : ∀ i, C.data.IsSimple (V i)) :
    InHomogeneousSpan C S X ↔ ∀ i, SameParityOrbit C.data S (V i) := by
  constructor
  · intro hX i
    have hi : d.data.inclusion i ≠ C.data.zero := by
      intro hz
      have hdiag := d.laws.diagonal i
      rw [hz, raw_zero_comp C.laws] at hdiag
      exact simple_id_ne_zero C.laws (hV i) hdiag.symm
    exact (sameParityOrbit_of_nonzero_to_span C hS (hV i) hX (d.data.inclusion i)
      (d.laws.inclusion_even i) hi).symm
  · intro hV
    obtain ⟨e, he⟩ := exists_homogeneousSum C.laws hV ((hasDecomposition_iff C X V).mpr ⟨d⟩)
    exact ⟨n, ⟨⟨e, he⟩⟩⟩

/-- Any specified homogeneous retract remains in the same component. -/
theorem inHomogeneousSpan_of_retract (hS : C.data.IsSimple S) (hX : InHomogeneousSpan C S X)
    {a : ZMod 2} (i : C.data.Hom Y X) (p : C.data.Hom X Y)
    (hip : C.data.comp i p = C.data.id Y) (hi : C.data.IsHomogeneous a i) :
    InHomogeneousSpan C S Y := by
  let d := simpleDecomposition C Y
  apply (inHomogeneousSpan_iff_simple_decomposition C hS d.toDecomposition d.laws.simple).mpr
  intro j
  have hj : d.data.decomposition.inclusion j ≠ C.data.zero := by
    intro hz
    have hdiag := d.laws.decomposition.diagonal j
    rw [hz, raw_zero_comp C.laws] at hdiag
    exact simple_id_ne_zero C.laws (d.laws.simple j) hdiag.symm
  have hne := comp_ne_zero_of_left_inverse C (d.data.decomposition.inclusion j) i p hip hj
  exact (sameParityOrbit_of_nonzero_to_span C hS (d.laws.simple j) hX
    (C.data.comp (d.data.decomposition.inclusion j) i)
    (C.laws.comp_grade _ _ (d.laws.decomposition.inclusion_even j) hi) hne).symm

end RMod.Classification
