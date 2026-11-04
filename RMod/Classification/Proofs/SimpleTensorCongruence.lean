import RMod.Classification.Proofs.SimpleTensorRepresentative
import RMod.Classification.Proofs.HomogeneousSumDetection
import RMod.Classification.Proofs.HomogeneousSums
import RMod.Classification.Proofs.Functors
import RMod.Classification.Instances.TensorFunctors

/-!
# Independence of tensor constituents from parity representatives

Tensoring with a fixed object is an ordinary superfunctor, so successive
whiskering carries homogeneous isomorphisms to a homogeneous isomorphism
of tensor products. Postcomposing the selected constituent inclusion
remains nonzero and therefore identifies the two selected parity orbits.
The full tensor product is also a homogeneous sum of its representative.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{0, 0})

theorem SameParityOrbit.tensor {X X' Y Y' : C.data.Obj}
    (hX : SameParityOrbit C.data X X') (hY : SameParityOrbit C.data Y Y') :
    SameParityOrbit C.data (C.data.tensorObj X Y) (C.data.tensorObj X' Y') := by
  obtain ⟨a, ha⟩ := hX
  obtain ⟨b, hb⟩ := hY
  exact ⟨a + b, homogeneousIso_trans C.laws
    ((tensorRightSuperfunctor C Y).map_homogeneousIso ha)
    ((tensorLeftSuperfunctor C X').map_homogeneousIso hb)⟩

theorem simpleTensorRepresentative_congr (X X' Y Y' : SimpleObject C)
    (hX : SameParityOrbit C.data X.data.object X'.data.object)
    (hY : SameParityOrbit C.data Y.data.object Y'.data.object) :
    SameParityOrbit C.data (simpleTensorRepresentative C X Y).data.object
      (simpleTensorRepresentative C X' Y').data.object := by
  obtain ⟨a, f, p, hfp, _, hf, _⟩ := SameParityOrbit.tensor C hX hY
  let d := simpleDecomposition C (C.data.tensorObj X.data.object Y.data.object)
  let i := d.data.decomposition.inclusion (tensorSimpleIndex C X Y)
  have hi : C.data.IsHomogeneous 0 i := d.laws.decomposition.inclusion_even _
  have hif := C.laws.comp_grade i f hi hf
  rw [zero_add] at hif
  exact simple_orbit_of_map_to_tensor C X' Y' (simpleTensorRepresentative C X Y).laws.simple
    (C.data.comp i f) hif
    (comp_ne_zero_of_left_inverse C i f p hfp (tensor_representative_inclusion_ne_zero C X Y))

theorem tensorRepresentative_homogeneousSum (X Y : SimpleObject C) :
    Nonempty (HomogeneousSum C.data (simpleTensorRepresentative C X Y).data.object
      (C.data.tensorObj X.data.object Y.data.object)
      (simpleDecomposition C (C.data.tensorObj X.data.object Y.data.object)).data.size) := by
  let d := simpleDecomposition C (C.data.tensorObj X.data.object Y.data.object)
  have ho (i : Fin d.data.size) :
      SameParityOrbit C.data (simpleTensorRepresentative C X Y).data.object (d.data.summand i) :=
    simple_tensor_isotypic C X.data.object Y.data.object X.laws.simple Y.laws.simple
      d.hasDecomposition d.laws.simple (tensorSimpleIndex C X Y) i
  obtain ⟨d', hd'⟩ := exists_homogeneousSum C.laws ho d.hasDecomposition
  exact ⟨⟨d', hd'⟩⟩

end RMod.Classification
