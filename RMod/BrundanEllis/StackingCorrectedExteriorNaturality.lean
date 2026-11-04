import RMod.BrundanEllis.StackingCorrectedExteriorTensorator
import RMod.BrundanEllis.StackingExternalBinaryNaturality
import RMod.BrundanEllis.StackingExternalTensoratorInsertions
import RMod.BrundanEllis.StackingExternalEnrichedTensorNaturality
import RMod.BrundanEllis.StackingExternalTotalTensorNaturality

/-! Naturality of the gauge-corrected exterior comparison on homogeneous coordinates, graded Hom objects, and full total Hom spaces. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace RMod.BrundanEllis.Stacking
open RMod.Classification Superfusion.RMod.RawDCT

/-- On homogeneous maps the only remaining sign exchanges an s-map with a t-map. -/
theorem correctedExteriorBinary_naturality (s t : Twist)
    (X X₁ X' X₁' : pullback s) (Y Y₁ Y' Y₁' : pullback t)
    (f : PullbackHom reference.data (oldTwist s).data X X₁)
    (f' : PullbackHom reference.data (oldTwist s).data X' X₁')
    (q : PullbackHom reference.data (oldTwist t).data Y Y₁)
    (q' : PullbackHom reference.data (oldTwist t).data Y' Y₁')
    (i i' j j' : ZMod 2)
    (hf : ∀ g, reference.data.IsHomogeneous i (f g))
    (hf' : ∀ g, reference.data.IsHomogeneous i' (f' g))
    (hq : ∀ h, reference.data.IsHomogeneous j (q h))
    (hq' : ∀ h, reference.data.IsHomogeneous j' (q' h))
    (g g' : s.group) (h h' : t.group) :
    reference.data.comp
      (twistSummandHom reference.data (oldTwist (exteriorTwist s t).val).data
        (X := (reversedExteriorPairing s t).obj (X, Y))
        (X' := (reversedExteriorPairing s t).obj (X₁, Y₁))
        (Y := (reversedExteriorPairing s t).obj (X', Y'))
        (Y' := (reversedExteriorPairing s t).obj (X₁', Y₁'))
        (fun gh => reference.data.tensorHom (q gh.2) (f gh.1))
        (fun gh => reference.data.tensorHom (q' gh.2) (f' gh.1)) (g, h) (g', h'))
      (correctedExteriorBinaryData s t X₁ X₁' Y₁ Y₁' g g' h h').hom =
    reference.data.smul (paritySign (i * j'))
      (reference.data.comp (correctedExteriorBinaryData s t X X' Y Y' g g' h h').hom
        (reference.data.tensorHom
          (twistSummandHom reference.data (oldTwist t).data q q' h h')
          (twistSummandHom reference.data (oldTwist s).data f f' g g'))) := by
  let hR := referenceProperty.toWeaklyPointedSuperfusionLaws
  dsimp only [correctedExteriorBinaryData, IsoData.scale]
  rw [hR.comp_smul, exteriorBinaryBlock_naturality s t X X₁ X' X₁' Y Y₁ Y' Y₁'
    f f' q q' i i' j j' hf hf' hq hq', hR.smul_comp,
    ← hR.mul_smul, ← hR.mul_smul, mul_comm]

end RMod.BrundanEllis.Stacking

namespace RMod.BrundanEllis.Stacking
open RMod.Classification CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

/-- The assembled even comparison agrees with the prescribed block on each summand. -/
theorem correctedExteriorTensoratorEvenIso_inclusion (s t : Twist) (X X' : pullback s) (Y Y' : pullback t)
    (g a : s.group) (h b : t.group) :
    convolutionInclusionEven reference.data referenceProperty (oldTwist (exteriorTwist s t).val).data
      ((reversedExteriorPairing s t).obj (X, Y)) ((reversedExteriorPairing s t).obj (X', Y')) (g, h) (a, b) ≫
        (correctedExteriorTensoratorEvenIso s t X X' Y Y' g h).hom =
    (correctedExteriorConvolutionBlockIso s t X X' Y Y' g h (a, b)).hom ≫
      (convolutionInclusionEven reference.data referenceProperty (oldTwist t).data Y Y' h b ⊗ₘ
        convolutionInclusionEven reference.data referenceProperty (oldTwist s).data X X' g a) := by
  simp only [convolutionInclusionEven, correctedExteriorTensoratorEvenIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc, biproduct.mapIso_hom, biproduct.ι_map_assoc]
  exact congrArg (fun f => (correctedExteriorConvolutionBlockIso s t X X' Y Y' g h (a, b)).hom ≫ f)
    (exteriorConvolutionExpand_inclusion_inv s t X X' Y Y' g a h b)

/-- The same block formula holds on the full graded Hom carrier. -/
theorem correctedExteriorTensorator_inclusion (s t : Twist) (X X' : pullback s) (Y Y' : pullback t)
    (g a : s.group) (h b : t.group) :
    reference.data.comp
      (convolutionInclusion reference.data referenceProperty (oldTwist (exteriorTwist s t).val).data
        ((reversedExteriorPairing s t).obj (X, Y)) ((reversedExteriorPairing s t).obj (X', Y')) (g, h) (a, b))
      (correctedExteriorTensoratorData s t X X' Y Y' g h).hom =
    reference.data.comp (correctedExteriorBinaryData s t X X' Y Y' a (a⁻¹ * g) b (b⁻¹ * h)).hom
      (reference.data.tensorHom
        (convolutionInclusion reference.data referenceProperty (oldTwist t).data Y Y' h b)
        (convolutionInclusion reference.data referenceProperty (oldTwist s).data X X' g a)) :=
  congrArg (fun f => f.hom) (correctedExteriorTensoratorEvenIso_inclusion s t X X' Y Y' g a h b)

end RMod.BrundanEllis.Stacking

namespace RMod.BrundanEllis.Stacking
open RMod.Classification Superfusion.RMod.RawDCT

/-- The full exterior comparison is natural on all homogeneous coordinate maps. -/
theorem correctedExteriorTensorator_naturality (s t : Twist)
    (X X₁ X' X₁' : pullback s) (Y Y₁ Y' Y₁' : pullback t)
    (f : PullbackHom reference.data (oldTwist s).data X X₁)
    (f' : PullbackHom reference.data (oldTwist s).data X' X₁')
    (q : PullbackHom reference.data (oldTwist t).data Y Y₁)
    (q' : PullbackHom reference.data (oldTwist t).data Y' Y₁')
    (i i' j j' : ZMod 2)
    (hf : ∀ g, reference.data.IsHomogeneous i (f g))
    (hf' : ∀ g, reference.data.IsHomogeneous i' (f' g))
    (hq : ∀ h, reference.data.IsHomogeneous j (q h))
    (hq' : ∀ h, reference.data.IsHomogeneous j' (q' h))
    (g : s.group) (h : t.group) :
    reference.data.comp
      (convolutionHom reference.data referenceProperty (oldTwist (exteriorTwist s t).val).data
        (X := (reversedExteriorPairing s t).obj (X, Y))
        (X' := (reversedExteriorPairing s t).obj (X₁, Y₁))
        (Y := (reversedExteriorPairing s t).obj (X', Y'))
        (Y' := (reversedExteriorPairing s t).obj (X₁', Y₁'))
        (fun gh => reference.data.tensorHom (q gh.2) (f gh.1))
        (fun gh => reference.data.tensorHom (q' gh.2) (f' gh.1)) (g, h))
      (correctedExteriorTensoratorData s t X₁ X₁' Y₁ Y₁' g h).hom =
    reference.data.smul (paritySign (i * j'))
      (reference.data.comp (correctedExteriorTensoratorData s t X X' Y Y' g h).hom
        (reference.data.tensorHom
          (convolutionHom reference.data referenceProperty (oldTwist t).data q q' h)
          (convolutionHom reference.data referenceProperty (oldTwist s).data f f' g))) := by
  let hC := referenceProperty.toWeaklyPointedSuperfusionLaws
  apply hom_ext_of_convolutionInclusions reference.data referenceProperty
    (oldTwist (exteriorTwist s t).val).data
    ((reversedExteriorPairing s t).obj (X, Y)) ((reversedExteriorPairing s t).obj (X', Y')) (g, h)
  rintro ⟨a, b⟩
  rw [← hC.comp_assoc, convolutionInclusion_map, hC.comp_assoc, correctedExteriorTensorator_inclusion]
  rw [← hC.comp_assoc]
  erw [correctedExteriorBinary_naturality s t X X₁ X' X₁' Y Y₁ Y' Y₁'
    f f' q q' i i' j j' hf hf' hq hq' a (a⁻¹ * g) b (b⁻¹ * h), hC.smul_comp, hC.comp_assoc]
  rw [hC.comp_smul]
  conv_rhs =>
    rw [← hC.comp_assoc, correctedExteriorTensorator_inclusion, hC.comp_assoc]
  congr 2
  rw [interchange_second_even hC _ _ _ _
      (convolutionInclusion_grade reference.data referenceProperty (oldTwist s).data X₁ X₁' g a),
    interchange_first_even hC _ _ _ _
      (convolutionInclusion_grade reference.data referenceProperty (oldTwist t).data Y Y' h b),
    convolutionInclusion_map, convolutionInclusion_map]

end RMod.BrundanEllis.Stacking

open CategoryTheory CategoryTheory.MonoidalCategory
open GradedObject.Monoidal
namespace RMod.BrundanEllis.Stacking
open RMod.Legacy RMod.Classification

attribute [local irreducible] reversedExteriorPairing correctedReversedExteriorTensorIso

set_option maxHeartbeats 1000000 in
/-- The whole tensor comparison is natural as an equation of graded Hom maps. -/
theorem correctedReversedExteriorTensorIso_enriched_naturality (s t : Twist)
    (X X' Y Y' : Even (SuperTensorProduct (pullback s) (pullback t))) :
    let F := reversedExteriorPairing s t
    (F.map X X' ⊗ₘ F.map Y Y') ≫
      enrichedTensorMap (C := exteriorModel s t) MonoidalSuperCategory.tensor
        MonoidalSuperCategory.tensor_objects (F.obj X) (F.obj X') (F.obj Y) (F.obj Y') ≫
      eHomWhiskerLeft SuperVec (F.forget.obj X ⊗ F.forget.obj Y)
        (correctedReversedExteriorTensorIso s t X' Y').hom =
    (productTensor (pullback s) (pullback t)).map (X, Y) (X', Y') ≫
      F.map (X ⊗ Y : Even (SuperTensorProduct (pullback s) (pullback t)))
      (X' ⊗ Y' : Even (SuperTensorProduct (pullback s) (pullback t))) ≫
      eHomWhiskerRight SuperVec (correctedReversedExteriorTensorIso s t X Y).hom
        (F.forget.obj (X' ⊗ Y')) := by
  dsimp only
  apply gradedFour_ext (SHom (pullback s) X.1 X'.1) (SHom (pullback t) X.2 X'.2)
    (SHom (pullback s) Y.1 Y'.1) (SHom (pullback t) Y.2 Y'.2)
  intro i j k l a ha f q f' q'
  apply Subtype.ext
  funext gh
  change (eHomWhiskerLeft SuperVec _ (correctedReversedExteriorTensorIso s t X' Y').hom a
    (enrichedTensorMap (C := exteriorModel s t) MonoidalSuperCategory.tensor
      MonoidalSuperCategory.tensor_objects _ _ _ _ a
      (((reversedExteriorPairing s t).map X X' ⊗ₘ (reversedExteriorPairing s t).map Y Y') a _))).val gh =
    (eHomWhiskerRight SuperVec (correctedReversedExteriorTensorIso s t X Y).hom _ a
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
  erw [correctedReversedExteriorTensorIso_hom s t X' Y' gh.1 gh.2,
    correctedReversedExteriorTensorIso_hom s t X Y gh.1 gh.2]
  erw [reversedExteriorPairing_value s t X X' i j (i + j) rfl f q,
    reversedExteriorPairing_value s t Y Y' k l (k + l) rfl f' q']
  with_unfolding_all
    change reference.data.comp
        (reference.data.smul ((-1 : ℝ) ^ ((i + j) * (k + l)).val) _)
        (correctedExteriorTensoratorData s t X'.1 Y'.1 X'.2 Y'.2 gh.1 gh.2).hom =
      reference.data.comp (correctedExteriorTensoratorData s t X.1 Y.1 X.2 Y.2 gh.1 gh.2).hom
        (reference.data.smul ((-1 : ℝ) ^ (j * k).val) _)
  erw [reversedExteriorPairing_tmul, pullbackTensor_tmul, pullbackTensor_tmul]
  let hC := referenceProperty.toWeaklyPointedSuperfusionLaws
  erw [hC.smul_comp, correctedExteriorTensorator_naturality s t X.1 X'.1 Y.1 Y'.1 X.2 X'.2 Y.2 Y'.2
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

open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
attribute [local irreducible] reversedExteriorPairing correctedReversedExteriorTensorIso

/-- The exterior comparison is natural on arbitrary, possibly inhomogeneous maps. -/
theorem correctedReversedExteriorTensorIso_total_naturality (s t : Twist)
    {X X' Y Y' : Even (SuperTensorProduct (pullback s) (pullback t))}
    (f : THom (SuperTensorProduct (pullback s) (pullback t)) X X')
    (g : THom (SuperTensorProduct (pullback s) (pullback t)) Y Y') :
    let F := reversedExteriorPairing s t
    tComp (exteriorModel s t)
      (tTensor (C := exteriorModel s t) MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects
        (tMap F f) (tMap F g))
      (evenPoint (correctedReversedExteriorTensorIso s t X' Y').hom) =
    tComp (exteriorModel s t) (evenPoint (correctedReversedExteriorTensorIso s t X Y).hom)
      (tMap F (tTensor (C := SuperTensorProduct (pullback s) (pullback t))
        MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects f g)) := by
  let F := reversedExteriorPairing s t
  let L := (F.map X X' ⊗ₘ F.map Y Y') ≫
    enrichedTensorMap (C := exteriorModel s t) MonoidalSuperCategory.tensor
      MonoidalSuperCategory.tensor_objects (F.obj X) (F.obj X') (F.obj Y) (F.obj Y')
  let R := (productTensor (pullback s) (pullback t)).map (X, Y) (X', Y') ≫
    F.map (X ⊗ Y : Even (SuperTensorProduct (pullback s) (pullback t)))
      (X' ⊗ Y' : Even (SuperTensorProduct (pullback s) (pullback t)))
  have hn := homEquation_total (D := exteriorModel s t)
    (A := F.forget.obj X ⊗ F.forget.obj Y) (B := F.forget.obj X' ⊗ F.forget.obj Y')
    (A' := F.forget.obj (X ⊗ Y)) (B' := F.forget.obj (X' ⊗ Y')) L R
    (correctedReversedExteriorTensorIso s t X Y).hom (correctedReversedExteriorTensorIso s t X' Y').hom
    (by simpa only [L, R, F, Category.assoc] using
      correctedReversedExteriorTensorIso_enriched_naturality s t X X' Y Y')
    (RMod.Regression.tensorPoint f g)
  have hl : (fun a => L a (RMod.Regression.tensorPoint f g a)) =
      tTensor (C := exteriorModel s t) MonoidalSuperCategory.tensor
        MonoidalSuperCategory.tensor_objects (tMap F f) (tMap F g) := by
    funext a
    change enrichedTensorMap (C := exteriorModel s t) MonoidalSuperCategory.tensor
      MonoidalSuperCategory.tensor_objects _ _ _ _ a
      ((F.map X X' ⊗ₘ F.map Y Y') a (RMod.Regression.tensorPoint f g a)) = _
    rw [congrFun (RMod.Regression.tensorPoint_map (F.map X X') (F.map Y Y') f g) a]
    rfl
  erw [hl] at hn
  exact hn

end RMod.BrundanEllis.Stacking
