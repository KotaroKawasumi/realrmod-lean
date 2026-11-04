import RMod.Classification.Instances.SimpleTensorRepresentative
import RMod.Classification.Proofs.Isotypy

/-!
# Detecting the intrinsic orbit of a tensor constituent

A nonzero homogeneous map from a simple to the tensor product has a
nonzero coefficient in its chosen simple decomposition. Schur identifies
that simple with the corresponding summand; tensor isotypy identifies
the summand with the representative selected for orbit multiplication.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{0, 0}) (X Y : SimpleObject C)

theorem simple_orbit_of_map_to_tensor {S : C.data.Obj} (hS : C.data.IsSimple S) {a : ZMod 2}
    (f : C.data.Hom S (C.data.tensorObj X.data.object Y.data.object))
    (hf : C.data.IsHomogeneous a f) (hne : f ≠ C.data.zero) :
    SameParityOrbit C.data S (simpleTensorRepresentative C X Y).data.object := by
  let d := simpleDecomposition C (C.data.tensorObj X.data.object Y.data.object)
  have hex : ∃ j, C.data.comp f (d.data.decomposition.projection j) ≠ C.data.zero := by
    by_contra h
    apply hne
    apply hom_ext_of_projections C.laws d.data.decomposition.inclusion d.data.decomposition.projection
      d.laws.decomposition.total
    intro j
    have hz : C.data.comp f (d.data.decomposition.projection j) = C.data.zero := by
      by_contra hj
      exact h ⟨j, hj⟩
    rw [hz, raw_zero_comp C.laws]
  obtain ⟨j, hj⟩ := hex
  have hg := C.laws.comp_grade f (d.data.decomposition.projection j) hf
    (d.laws.decomposition.projection_even j)
  rw [add_zero] at hg
  have hs : SameParityOrbit C.data S (d.data.summand j) :=
    ⟨a, homogeneous_schur C.laws hS (d.laws.simple j) _ hg hj⟩
  exact SameParityOrbit.trans C.laws hs
    (simple_tensor_isotypic C X.data.object Y.data.object X.laws.simple Y.laws.simple
      d.hasDecomposition d.laws.simple j (tensorSimpleIndex C X Y))

theorem tensor_representative_inclusion_ne_zero :
    (simpleDecomposition C (C.data.tensorObj X.data.object Y.data.object)).data.decomposition.inclusion
      (tensorSimpleIndex C X Y) ≠ C.data.zero := by
  intro hz
  have hh := (simpleDecomposition C (C.data.tensorObj X.data.object Y.data.object)).laws.decomposition.diagonal
    (tensorSimpleIndex C X Y)
  rw [hz, raw_zero_comp C.laws] at hh
  exact simple_id_ne_zero C.laws (simpleTensorRepresentative C X Y).laws.simple hh.symm

end RMod.Classification
