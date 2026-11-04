import RMod.Classification.Instances.SimpleOrbitMultiplication
import RMod.Classification.Instances.HomogeneousSumMap

/-!
# Associativity on simple parity classes

A constituent of `(X ⊗ Y) ⊗ Z` maps nontrivially through the actual
associator into `X ⊗ (Y ⊗ Z)`. A homogeneous sum presentation of `Y ⊗ Z`
detects this map on one copy of its chosen constituent. Graded Schur then
identifies the resulting simple class with the other parenthesization.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{0, 0}) (X Y Z : SimpleObject C)

theorem simpleTensorRepresentative_assoc :
    SameParityOrbit C.data
      (simpleTensorRepresentative C (simpleTensorRepresentative C X Y) Z).data.object
      (simpleTensorRepresentative C X (simpleTensorRepresentative C Y Z)).data.object := by
  let R := simpleTensorRepresentative C X Y
  let d := simpleDecomposition C (C.data.tensorObj X.data.object Y.data.object)
  let e := simpleDecomposition C (C.data.tensorObj R.data.object Z.data.object)
  let i := e.data.decomposition.inclusion (tensorSimpleIndex C R Z)
  let F := tensorRightSuperfunctor C Z.data.object
  let j := F.data.map (d.data.decomposition.inclusion (tensorSimpleIndex C X Y))
  let p := F.data.map (d.data.decomposition.projection (tensorSimpleIndex C X Y))
  have hjp : C.data.comp j p = C.data.id (C.data.tensorObj R.data.object Z.data.object) := by
    dsimp only [j, p]
    rw [← F.laws.map_comp, d.laws.decomposition.diagonal, F.laws.map_id]
    rfl
  have hi := tensor_representative_inclusion_ne_zero C R Z
  have hij := comp_ne_zero_of_left_inverse C i j p hjp hi
  let a := C.data.associatorHom X.data.object Y.data.object Z.data.object
  let ai := C.data.associatorInv X.data.object Y.data.object Z.data.object
  have hna := comp_ne_zero_of_left_inverse C (C.data.comp i j) a ai
    (C.laws.associator_hom_inv _ _ _) hij
  have hig : C.data.IsHomogeneous 0 i := e.laws.decomposition.inclusion_even _
  have hjg : C.data.IsHomogeneous 0 j := F.laws.map_grade _ (d.laws.decomposition.inclusion_even _)
  have hag : C.data.IsHomogeneous 0 a := C.laws.associator_hom_even _ _ _
  have hfg := C.laws.comp_grade (C.data.comp i j) a (C.laws.comp_grade i j hig hjg) hag
  simp only [zero_add] at hfg
  obtain ⟨s⟩ := tensorRepresentative_homogeneousSum C Y Z
  let t := s.map (tensorLeftSuperfunctor C X.data.object)
  obtain ⟨k, hk⟩ := t.exists_nonzero_projection C (C.data.comp (C.data.comp i j) a) hna
  have hkg := C.laws.comp_grade _ (t.data.projection k) hfg (t.laws.projection_grade k)
  rw [zero_add] at hkg
  exact simple_orbit_of_map_to_tensor C X (simpleTensorRepresentative C Y Z)
    (simpleTensorRepresentative C R Z).laws.simple _ hkg hk

theorem simpleOrbitMul_assoc (x y z : SimpleOrbit C) :
    simpleOrbitMul C (simpleOrbitMul C x y) z = simpleOrbitMul C x (simpleOrbitMul C y z) := by
  refine Quotient.inductionOn₃ x y z ?_
  intro X Y Z
  exact Quotient.sound (simpleTensorRepresentative_assoc C X Y Z)

end RMod.Classification
