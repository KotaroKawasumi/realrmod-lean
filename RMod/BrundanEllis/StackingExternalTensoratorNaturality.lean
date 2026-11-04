import RMod.BrundanEllis.StackingExternalBinaryNaturality
import RMod.BrundanEllis.StackingExternalTensoratorInsertions

/-! Naturality of the finite-sum tensor comparison follows from its actual
summand inclusions and the proved homogeneous block formula. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace RMod.BrundanEllis.Stacking
open RMod.Classification Superfusion.RMod.RawDCT

/-- The full exterior comparison is natural on all homogeneous coordinate maps. -/
theorem exteriorTensorator_naturality (s t : Twist)
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
      (exteriorTensoratorData s t X₁ X₁' Y₁ Y₁' g h).hom =
    reference.data.smul (paritySign (i * j'))
      (reference.data.comp (exteriorTensoratorData s t X X' Y Y' g h).hom
        (reference.data.tensorHom
          (convolutionHom reference.data referenceProperty (oldTwist t).data q q' h)
          (convolutionHom reference.data referenceProperty (oldTwist s).data f f' g))) := by
  let hC := referenceProperty.toWeaklyPointedSuperfusionLaws
  apply hom_ext_of_convolutionInclusions reference.data referenceProperty
    (oldTwist (exteriorTwist s t).val).data
    ((reversedExteriorPairing s t).obj (X, Y)) ((reversedExteriorPairing s t).obj (X', Y')) (g, h)
  rintro ⟨a, b⟩
  rw [← hC.comp_assoc, convolutionInclusion_map, hC.comp_assoc, exteriorTensorator_inclusion]
  rw [← hC.comp_assoc]
  erw [exteriorBinaryBlock_naturality s t X X₁ X' X₁' Y Y₁ Y' Y₁'
    f f' q q' i i' j j' hf hf' hq hq' a (a⁻¹ * g) b (b⁻¹ * h), hC.smul_comp, hC.comp_assoc]
  rw [hC.comp_smul]
  conv_rhs =>
    rw [← hC.comp_assoc, exteriorTensorator_inclusion, hC.comp_assoc]
  congr 2
  rw [interchange_second_even hC _ _ _ _
      (convolutionInclusion_grade reference.data referenceProperty (oldTwist s).data X₁ X₁' g a),
    interchange_first_even hC _ _ _ _
      (convolutionInclusion_grade reference.data referenceProperty (oldTwist t).data Y Y' h b),
    convolutionInclusion_map, convolutionInclusion_map]

end RMod.BrundanEllis.Stacking
