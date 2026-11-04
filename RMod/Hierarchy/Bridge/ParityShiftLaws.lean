import RMod.Hierarchy.Bridge.ParityShiftData
import RMod.Hierarchy.Instances.HomogeneousBasis
import RMod.Hierarchy.Instances.GradedTensorPoints

/-!
# Odd enriched naturality of the parity shift

The center braiding contributes the sign of the tested homogeneous map.
Evaluation on the odd line's basis gives the old inverse naturality law;
all other components vanish. The inverse equations retain the old maps.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
open GradedObject.Monoidal
open scoped TensorProduct
namespace RMod.Legacy.Hierarchy
variable (C : WeaklyPointedSuperfusion.{0, 0}) (p : Classification.Pi C.data)

theorem ofOldParity_naturality (X Y : C.data.Obj) :
    koszulMap oddLine (oldEnrichedHom C X Y) ≫
      (𝟙 (oldEnrichedHom C X Y) ⊗ₘ (ofOldParityShiftData C p).hom Y) ≫
        oldEnrichedComp C X Y (p.data.shiftObj Y) =
      ((ofOldParityShiftData C p).hom X ⊗ₘ (ofOldParityShiftData C p).functor.map X Y) ≫
        oldEnrichedComp C X (p.data.shiftObj X) (p.data.shiftObj Y) := by
  funext a
  apply tensorObj_ext
  intro i j hij
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f g
  by_cases hi : i = 1
  · subst i
    rw [homogeneousLine_smul_basis 1 f]
    erw [← TensorProduct.smul_tmul']
    simp only [map_smul]
    congr 1
    let b := (GradedObject.singleObjApplyIso (1 : ZMod 2) (ModuleCat.of ℝ ℝ)).inv 1
    change oldEnrichedComp C X Y (p.data.shiftObj Y) a
      ((𝟙 (oldEnrichedHom C X Y) ⊗ₘ (ofOldParityShiftData C p).hom Y) a
        (koszulMap oddLine (oldEnrichedHom C X Y) a
          (gradedTmul oddLine (oldEnrichedHom C X Y) 1 j a hij b g))) =
      oldEnrichedComp C X (p.data.shiftObj X) (p.data.shiftObj Y) a
        (((ofOldParityShiftData C p).hom X ⊗ₘ (ofOldParityShiftData C p).functor.map X Y) a
          (gradedTmul oddLine (oldEnrichedHom C X Y) 1 j a hij b g))
    erw [koszulMap_gradedTmul oddLine (oldEnrichedHom C X Y) 1 j a hij b g,
      map_smul, map_smul, tensorHom_gradedTmul, tensorHom_gradedTmul]
    apply Subtype.ext
    change C.data.smul ((-1 : ℝ) ^ (1 * j).val)
      (oldEnrichedComp C X Y (p.data.shiftObj Y) a
        (gradedTmul _ _ j 1 a _ g ((ofOldParityShiftData C p).hom Y 1 b))).val = _
    unfold gradedTmul
    erw [oldEnrichedComp_tmul C X Y (p.data.shiftObj Y),
      oldEnrichedComp_tmul C X (p.data.shiftObj X) (p.data.shiftObj Y)]
    have he (Z : C.data.Obj) : ((ofOldParityShiftData C p).hom Z 1 b).val = p.data.zInv Z := by
      exact congrArg (fun u : Classification.LinearCategory.grade C Z (p.data.shiftObj Z) 1 => u.val)
        (homogeneousPoint_map_same (oldEnrichedHom C Z (p.data.shiftObj Z)) 1
          ⟨p.data.zInv Z, p.laws.z_inv_odd C.laws Z⟩)
    rw [he, he, one_mul]
    exact (oldParity_inverse_naturality C p j g.val g.property).symm
  · haveI : Subsingleton (oddLine i) := homogeneousLine_subsingleton 1 i hi
    rw [Subsingleton.elim f 0]
    simp only [TensorProduct.zero_tmul, map_zero]

theorem ofOldParityShiftLaws : ParityShiftLaws (ofOldSupercategory C) (ofOldParityShiftData C p) where
  functor := ofOldSuperfunctorLaws (Classification.tensorLeftSuperfunctor C p.data.object)
  naturality := ⟨{
    app := (ofOldParityShiftData C p).hom
    naturality := ofOldParity_naturality C p }, rfl⟩
  hom_inv X := by
    apply (totalHomEquiv C _ _).injective
    erw [totalHomEquiv_comp C X (p.data.shiftObj X) X, totalHomEquiv_id C X]
    dsimp only [ofOldParityShiftData]
    erw [totalHomEquiv_homogeneousMap C, totalHomEquiv_homogeneousMap C]
    exact (p.laws.z_iso C.laws X).inv_hom
  inv_hom X := by
    apply (totalHomEquiv C _ _).injective
    erw [totalHomEquiv_comp C (p.data.shiftObj X) X (p.data.shiftObj X),
      totalHomEquiv_id C (p.data.shiftObj X)]
    dsimp only [ofOldParityShiftData]
    erw [totalHomEquiv_homogeneousMap C, totalHomEquiv_homogeneousMap C]
    exact (p.laws.z_iso C.laws X).hom_inv

def ofOldPiSupercategory : PiSupercategory :=
  ⟨⟨ofOldSupercategoryData C, ofOldParityShiftData C p⟩,
    ⟨ofOldSupercategoryLaws C, ofOldParityShiftLaws C p⟩⟩

end RMod.Legacy.Hierarchy
