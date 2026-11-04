import RMod.Classification.Instances.GaugeNamedBinaryComparison
import RMod.Classification.Proofs.GaugeNamedComparisonMaps
import RMod.Classification.Proofs.IndexedComparisonEquality
import RMod.Classification.Proofs.EquivalenceGaugeRatio

/-!
# The extracted binary ratio at named group coordinates

The component comparisons, tensorator, and source evaluation are the
same maps as before, with their endpoint indices identified. Transport
the full binary identity using heterogeneous equality; this preserves the
single retained scalar on every pair of objects in the two components.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (twistedPullback C hC t).toWeaklyPointedSuperfusion)
  (g h : s.data.group)
  (X : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (pullbackDegreeSimple C hC s g).data.object)
  (Y : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (pullbackDegreeSimple C hC s h).data.object)

theorem pullbackDegreeSimple_tensorDegree :
    pullbackSimpleDegree C hC s
      (simpleTensorRepresentative (twistedPullback C hC s).toWeaklyPointedSuperfusion
        (pullbackDegreeSimple C hC s g) (pullbackDegreeSimple C hC s h)) = g * h := by
  rw [pullbackSimpleDegree_tensor, pullbackSimpleDegree_placed, pullbackSimpleDegree_placed]

theorem pullbackTensorComparison_named_heq :
    HEq ((pullbackTensorComparison C hC s (pullbackDegreeSimple C hC s g)
      (pullbackDegreeSimple C hC s h)).data.app X Y).hom
      (convolutionIndexedComparisonData C hC s.data X.obj Y.obj g h (g * h) rfl).hom := by
  exact convolutionIndexedComparison_hom_heq C hC s.data X.obj Y.obj
    (pullbackSimpleDegree_placed C hC s g) (pullbackSimpleDegree_placed C hC s h)
    (pullbackDegreeSimple_tensorDegree C hC s g h)
    (pullbackSimpleDegree_tensor C hC s (pullbackDegreeSimple C hC s g)
      (pullbackDegreeSimple C hC s h)).symm rfl

theorem equivalenceTensorComparison_named_heq :
    HEq ((equivalenceTensorComparison C hC s t E (pullbackDegreeSimple C hC s g)
      (pullbackDegreeSimple C hC s h)).data.app X Y).hom
      (equivalenceIndexedComparisonData C hC s t E X.obj Y.obj
        (equivalenceGaugePhi C hC s t E g) (equivalenceGaugePhi C hC s t E h)
        (equivalenceGaugePhi C hC s t E (g * h))
        (map_mul (equivalenceGaugePhi C hC s t E) g h).symm).hom := by
  let S := pullbackDegreeSimple C hC s g
  let T := pullbackDegreeSimple C hC s h
  let R := simpleTensorRepresentative (twistedPullback C hC s).toWeaklyPointedSuperfusion S T
  have hu : pullbackSimpleDegree C hC t (E.mapSimple R) = equivalenceGaugePhi C hC s t E (g * h) :=
    (equivalenceSimpleDegree C hC s t E R).trans
      (congrArg (equivalenceGaugePhi C hC s t E) (pullbackDegreeSimple_tensorDegree C hC s g h))
  exact equivalenceIndexedComparison_hom_heq C hC s t E X.obj Y.obj
    (equivalenceGaugePhi_apply C hC s t E g).symm (equivalenceGaugePhi_apply C hC s t E h).symm hu
    (inv_mul_eq_iff_eq_mul.mp (equivalenceTensorRightDegree_eq C hC s t E S T)).symm
    (map_mul (equivalenceGaugePhi C hC s t E) g h).symm

theorem equivalenceTensorComponentComparison_named_inv_heq :
    HEq ((equivalenceTensorComponentComparison C hC s t E
      (pullbackDegreeSimple C hC s g) (pullbackDegreeSimple C hC s h)).data.inv.app
        (spanTensorObj (twistedPullback C hC s).toWeaklyPointedSuperfusion
          (pullbackDegreeSimple C hC s g) (pullbackDegreeSimple C hC s h) X Y)).hom
      (equivalenceNamedComparisonData C hC s t E (g * h)
        (pullbackNamedTensorSpanObj C hC s g h X Y)).inv := by
  let S := pullbackDegreeSimple C hC s g
  let T := pullbackDegreeSimple C hC s h
  let R := simpleTensorRepresentative (twistedPullback C hC s).toWeaklyPointedSuperfusion S T
  let V := spanTensorObj (twistedPullback C hC s).toWeaklyPointedSuperfusion S T X Y
  have hd := pullbackDegreeSimple_tensorDegree C hC s g h
  have he := equivalenceSimpleComparison_inv_degree C hC s t E R
    (pullbackSimpleDegree C hC s R) rfl (g * h) hd hd V
  exact (heq_of_eq he).trans
    (equivalenceSimpleComparison_named_inv_heq C hC s t E (g * h) R hd V)

theorem equivalenceChangedTensorComparison_named_heq :
    HEq ((equivalenceChangedTensorComparison C hC s t E g h).data.app X Y).hom
      (equivalenceNamedChangedComparisonData C hC s t E g h X Y).hom := by
  let R := simpleTensorRepresentative (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (pullbackDegreeSimple C hC s g) (pullbackDegreeSimple C hC s h)
  have hd := pullbackDegreeSimple_tensorDegree C hC s g h
  have he := (equivalenceSimpleDegree C hC s t E R).trans
    (congrArg (equivalenceGaugePhi C hC s t E) hd)
  let e₀ := congrArg (fun j => (convolutionObj C hC s.data X.obj Y.obj j).val) hd
  let e₁ := congrArg (fun j => (E.data.forward.obj
    ((twistedPullback C hC s).data.tensorObj X.obj Y.obj) j).val) he
  let ex := congrArg (fun j => (X.obj j).val) (pullbackSimpleDegree_placed C hC s g)
  let ey := congrArg (fun j => (Y.obj j).val) (pullbackSimpleDegree_placed C hC s h)
  exact rawHom_comp_heq (C := C.toWeaklyPointedSuperfusionData) e₀ rfl (congrArg₂ C.tensorObj ex ey)
    (rawHom_comp_heq (C := C.toWeaklyPointedSuperfusionData) e₀ e₁ rfl
      (equivalenceTensorComponentComparison_named_inv_heq C hC s t E g h X Y)
      (equivalenceTensorComparison_named_heq C hC s t E g h X Y))
    (rawHom_tensor_heq (C := C.toWeaklyPointedSuperfusionData) rfl ex rfl ey
      (equivalenceNamedComparison_hom_heq C hC s t E g X).symm
      (equivalenceNamedComparison_hom_heq C hC s t E h Y).symm)

end RMod.Classification
