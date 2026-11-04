import RMod.Hierarchy.Bridge.LegacyFusion
import RMod.Hierarchy.Bridge.LegacyInterchange
import RMod.Hierarchy.Bridge.LegacyNaturality
import RMod.Hierarchy.Bridge.LegacyRigidity
import RMod.Hierarchy.Bridge.LegacyWeakInvertibility

/-!
# Every new classification input has a legacy presentation

The data are extracted from the enriched total category, with the inverse
Koszul convention correction. Each legacy law follows from the specified
new laws or a Mathlib construction. The old classification theorems can
therefore be applied to arbitrary new inputs without an extra assumption.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.Legacy.Hierarchy
variable (A : WeaklyPointedFusionPiSupercategory)

theorem toOldLaws : WeaklyPointedSuperfusionLaws (toOldData A.toMonoidalPiSupercategory.monoidal) := by
  let C := A.toMonoidalPiSupercategory.monoidal
  change WeaklyPointedSuperfusionLaws (toOldData C)
  exact {
    comp_id := fun f => tComp_id_right C.super f
    id_comp := fun f => tComp_id_left C.super f
    comp_assoc := fun f g h => tComp_assoc C.super f g h
    add_assoc := fun {X Y} => @add_assoc (THom C.super.data X Y) _
    zero_add := fun {X Y} => @zero_add (THom C.super.data X Y) _
    add_zero := fun {X Y} => @add_zero (THom C.super.data X Y) _
    add_comm := fun {X Y} => @add_comm (THom C.super.data X Y) _
    neg_add := fun {X Y} => @neg_add_cancel (THom C.super.data X Y) _
    one_smul := fun {X Y} => @one_smul ℝ (THom C.super.data X Y) _ _
    mul_smul := fun {X Y} => @mul_smul ℝ (THom C.super.data X Y) _ _
    add_smul := fun {X Y} => @add_smul ℝ (THom C.super.data X Y) _ _ _
    smul_add := fun {X Y} (r : ℝ) (f g : THom C.super.data X Y) => smul_add r f g
    zero_smul := fun {X Y} => @zero_smul ℝ (THom C.super.data X Y) _ _ _
    smul_zero := fun {X Y} => @smul_zero ℝ (THom C.super.data X Y) _ _
    add_comp := fun f g h => tComp_add_left C.super.data f g h
    comp_add := fun f g h => tComp_add_right C.super.data f g h
    smul_comp := fun r f g => tComp_smul_left C.super.data r f g
    comp_smul := fun r f g => tComp_smul_right C.super.data r f g
    grade_zero := fun X Y a => (grade C.super X Y a).zero_mem
    grade_add := fun {X Y a} f g hf hg => (grade C.super X Y a).add_mem hf hg
    grade_neg := fun {X Y a} f hf => (grade C.super X Y a).neg_mem hf
    grade_smul := fun {X Y a} r f hf => (grade C.super X Y a).smul_mem r hf
    grade_decomposition := fun f => ⟨homogeneousPart C.super 0 f, homogeneousPart C.super 1 f,
      homogeneousPart_mem C.super 0 f, homogeneousPart_mem C.super 1 f, homogeneousPart_add C.super f⟩
    grade_disjoint := fun f hf hg => grade_disjoint C.super f hf hg
    id_even := fun X => evenPoint_mem_grade C.super (C.data.id X)
    comp_grade := fun f g hf hg => tComp_mem_grade C.super f g hf hg
    tensor_grade := fun f g hf hg => legacyTensor_mem_grade C f g hf hg
    tensor_id := legacyTensor_id C
    tensor_add_left := legacyTensor_add_left C
    tensor_add_right := legacyTensor_add_right C
    tensor_smul_left := legacyTensor_smul_left C
    tensor_smul_right := legacyTensor_smul_right C
    super_interchange := fun {X₁ Y₁ Z₁ X₂ Y₂ Z₂ b c} f g h k hg hh =>
      legacyTensor_interchange C c b h k f g hh hg
    associator_hom_inv := fun X Y Z => by
      have h := congrArg evenPoint (C.laws.monoidal.associator_hom_inv X Y Z)
      rw [evenPoint_comp] at h
      exact h
    associator_inv_hom := fun X Y Z => by
      have h := congrArg evenPoint (C.laws.monoidal.associator_inv_hom X Y Z)
      rw [evenPoint_comp] at h
      exact h
    associator_hom_even := fun X Y Z => evenPoint_mem_grade C.super (C.data.monoidal.associatorHom X Y Z)
    associator_inv_even := fun X Y Z => evenPoint_mem_grade C.super (C.data.monoidal.associatorInv X Y Z)
    associator_naturality := legacyAssociatorNaturality C
    left_unitor_hom_inv := fun X => by
      have h := congrArg evenPoint (C.laws.monoidal.left_hom_inv X)
      rw [evenPoint_comp] at h
      exact h
    left_unitor_inv_hom := fun X => by
      have h := congrArg evenPoint (C.laws.monoidal.left_inv_hom X)
      rw [evenPoint_comp] at h
      exact h
    left_unitor_hom_even := fun X => evenPoint_mem_grade C.super (C.data.monoidal.leftHom X)
    left_unitor_inv_even := fun X => evenPoint_mem_grade C.super (C.data.monoidal.leftInv X)
    left_unitor_naturality := legacyLeftNaturality C
    right_unitor_hom_inv := fun X => by
      have h := congrArg evenPoint (C.laws.monoidal.right_hom_inv X)
      rw [evenPoint_comp] at h
      exact h
    right_unitor_inv_hom := fun X => by
      have h := congrArg evenPoint (C.laws.monoidal.right_inv_hom X)
      rw [evenPoint_comp] at h
      exact h
    right_unitor_hom_even := fun X => evenPoint_mem_grade C.super (C.data.monoidal.rightHom X)
    right_unitor_inv_even := fun X => evenPoint_mem_grade C.super (C.data.monoidal.rightInv X)
    right_unitor_naturality := legacyRightNaturality C
    pentagon := legacyPentagon C
    triangle := legacyTriangle C
    has_finite_biproducts := legacyFiniteBiproducts C
    semisimple := legacySemisimple A.toFusionPiSupercategory
    graded_schur := fun {X Y} hX hY {a} f hf hf₀ => legacyGradedSchur A.toFusionPiSupercategory hX hY (a := a) f hf hf₀
    finite_dimensional_hom := legacyFiniteBasis A.toFusionPiSupercategory
    finite_simple_representatives := legacyFiniteSimples A.toFusionPiSupercategory
    simple_unit := (legacySimple_iff C (evenObj C.super C.data.monoidal.unit)).mpr A.simple_unit
    unit_end_scalar_injective := legacyUnitScalarInjective A
    unit_end_scalar_surjective := legacyUnitScalarSurjective A
    has_right_dual := legacyRightDual A.toFusionPiSupercategory
    has_left_dual := legacyLeftDual A.toFusionPiSupercategory
    weakly_pointed := legacyWeaklyInvertible A }

def toOldPiSuperfusionData : Classification.PiSuperfusionData.{0, 0} where
  toWeaklyPointedSuperfusionData := toOldData A.toMonoidalPiSupercategory.monoidal
  pi := toOldParityData A.toMonoidalPiSupercategory

theorem toOldPiSuperfusionLaws : Classification.PiSuperfusionLaws (toOldPiSuperfusionData A) where
  toWeaklyPointedSuperfusionLaws := toOldLaws A
  pi := toOldParityLaws A.toMonoidalPiSupercategory

def toOldPiSuperfusion : Classification.PiSuperfusion.{0, 0} :=
  ⟨toOldPiSuperfusionData A, toOldPiSuperfusionLaws A⟩

end RMod.Legacy.Hierarchy
