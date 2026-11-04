import RMod.BrundanEllis.StackingExternalReversedPure
import RMod.BrundanEllis.StackingExternalEvenComparison
import RMod.BrundanEllis.StackingExternalTensorHomPoints
import RMod.BrundanEllis.StackingExternalTensoratorNaturality

/-! Homogeneous coordinate naturality determines the full enriched tensor
comparison. Its signs include the middle crossing in the product category
and both chronological tensor conventions. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open CategoryTheory CategoryTheory.MonoidalCategory
open GradedObject.Monoidal
namespace RMod.BrundanEllis.Stacking
open RMod.Legacy RMod.Classification

attribute [local irreducible] reversedExteriorPairing reversedExteriorTensorIso

set_option maxHeartbeats 1000000 in
/-- The whole tensor comparison is natural as an equation of graded Hom maps. -/
theorem reversedExteriorTensorIso_enriched_naturality (s t : Twist)
    (X X' Y Y' : Even (SuperTensorProduct (pullback s) (pullback t))) :
    let F := reversedExteriorPairing s t
    (F.map X X' ⊗ₘ F.map Y Y') ≫
      enrichedTensorMap (C := exteriorModel s t) MonoidalSuperCategory.tensor
        MonoidalSuperCategory.tensor_objects (F.obj X) (F.obj X') (F.obj Y) (F.obj Y') ≫
      eHomWhiskerLeft SuperVec (F.forget.obj X ⊗ F.forget.obj Y)
        (reversedExteriorTensorIso s t X' Y').hom =
    (productTensor (pullback s) (pullback t)).map (X, Y) (X', Y') ≫
      F.map (X ⊗ Y : Even (SuperTensorProduct (pullback s) (pullback t)))
      (X' ⊗ Y' : Even (SuperTensorProduct (pullback s) (pullback t))) ≫
      eHomWhiskerRight SuperVec (reversedExteriorTensorIso s t X Y).hom
        (F.forget.obj (X' ⊗ Y')) := by
  dsimp only
  apply gradedFour_ext (SHom (pullback s) X.1 X'.1) (SHom (pullback t) X.2 X'.2)
    (SHom (pullback s) Y.1 Y'.1) (SHom (pullback t) Y.2 Y'.2)
  intro i j k l a ha f q f' q'
  apply Subtype.ext
  funext gh
  change (eHomWhiskerLeft SuperVec _ (reversedExteriorTensorIso s t X' Y').hom a
    (enrichedTensorMap (C := exteriorModel s t) MonoidalSuperCategory.tensor
      MonoidalSuperCategory.tensor_objects _ _ _ _ a
      (((reversedExteriorPairing s t).map X X' ⊗ₘ (reversedExteriorPairing s t).map Y Y') a _))).val gh =
    (eHomWhiskerRight SuperVec (reversedExteriorTensorIso s t X Y).hom _ a
      ((reversedExteriorPairing s t).map
        (X ⊗ Y : Even (SuperTensorProduct (pullback s) (pullback t)))
        (X' ⊗ Y' : Even (SuperTensorProduct (pullback s) (pullback t))) a
        ((productTensor (pullback s) (pullback t)).map (X, Y) (X', Y') a _))).val gh
  erw [tensorHom_gradedTmul]
  erw [pullback_post_apply]
  erw [pullback_pre_apply]
  erw [pullbackTensor_tmul]
  erw [productTensor_tmul X X' Y Y' i j k l a ha f q f' q']
  erw [map_smul]
  erw [reversedExteriorTensorIso_hom s t X' Y' gh.1 gh.2,
    reversedExteriorTensorIso_hom s t X Y gh.1 gh.2]
  erw [reversedExteriorPairing_value s t X X' i j (i + j) rfl f q,
    reversedExteriorPairing_value s t Y Y' k l (k + l) rfl f' q']
  with_unfolding_all
    change reference.data.comp
        (reference.data.smul ((-1 : ℝ) ^ ((i + j) * (k + l)).val) _)
        (exteriorTensoratorData s t X'.1 Y'.1 X'.2 Y'.2 gh.1 gh.2).hom =
      reference.data.comp (exteriorTensoratorData s t X.1 Y.1 X.2 Y.2 gh.1 gh.2).hom
        (reference.data.smul ((-1 : ℝ) ^ (j * k).val) _)
  erw [reversedExteriorPairing_tmul, pullbackTensor_tmul, pullbackTensor_tmul]
  let hC := referenceProperty.toWeaklyPointedSuperfusionLaws
  erw [hC.smul_comp, exteriorTensorator_naturality s t X.1 X'.1 Y.1 Y'.1 X.2 X'.2 Y.2 Y'.2
    f.val f'.val q.val q'.val i k j l f.property f'.property q.property q'.property gh.1 gh.2]
  rw [hC.tensor_smul_left, hC.tensor_smul_right, hC.comp_smul, hC.comp_smul, hC.comp_smul]
  rw [ReferenceCommutor.paritySign_pow]
  simp only [← hC.mul_smul, ← parity_power_add]
  congr 1
  congr 1
  congr 1
  ring_nf
  simp [CharTwo.two_eq_zero]

end RMod.BrundanEllis.Stacking
