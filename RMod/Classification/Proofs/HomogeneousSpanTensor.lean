import RMod.Classification.Proofs.HomogeneousSpanMembership
import RMod.Classification.Proofs.SimpleTensorCongruence
import RMod.Classification.Instances.HomogeneousSumMap

/-!
# Tensor products land in the product simple-orbit component

For a simple constituent of X tensor Y, project first through a
homogeneous presentation of X and then through one of Y. Some composite
projection remains nonzero. Its target is the tensor product of the two
simple generators, whose intrinsic product orbit was already proved.
This determines every constituent's component without choosing tensor
matrix bases or adding any condition to the reference property.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem inHomogeneousSpan_tensor (C : WeaklyPointedSuperfusion.{0, 0})
    (S T : SimpleObject C) {X Y : C.data.Obj}
    (hX : InHomogeneousSpan C S.data.object X) (hY : InHomogeneousSpan C T.data.object Y) :
    InHomogeneousSpan C (simpleTensorRepresentative C S T).data.object (C.data.tensorObj X Y) := by
  obtain ⟨n, ⟨d⟩⟩ := hX
  obtain ⟨m, ⟨e⟩⟩ := hY
  let d' := d.map (tensorRightSuperfunctor C Y)
  let e' := e.map (tensorLeftSuperfunctor C S.data.object)
  let c := simpleDecomposition C (C.data.tensorObj X Y)
  apply (inHomogeneousSpan_iff_simple_decomposition C (simpleTensorRepresentative C S T).laws.simple
    c.toDecomposition c.laws.simple).mpr
  intro k
  let f := c.data.decomposition.inclusion k
  have hf : f ≠ C.data.zero := by
    intro hz
    have hdiag := c.laws.decomposition.diagonal k
    change C.data.comp f _ = _ at hdiag
    rw [hz, raw_zero_comp C.laws] at hdiag
    exact simple_id_ne_zero C.laws (c.laws.simple k) hdiag.symm
  obtain ⟨i, hi⟩ := d'.exists_nonzero_projection C f hf
  have hgi := C.laws.comp_grade f (d'.data.projection i)
    (c.laws.decomposition.inclusion_even k) (d'.laws.projection_grade i)
  obtain ⟨j, hj⟩ := e'.exists_nonzero_projection C (C.data.comp f (d'.data.projection i)) hi
  have hgj := C.laws.comp_grade _ _ hgi (e'.laws.projection_grade j)
  exact (simple_orbit_of_map_to_tensor C S T (c.laws.simple k) _ hgj hj).symm

end RMod.Classification
