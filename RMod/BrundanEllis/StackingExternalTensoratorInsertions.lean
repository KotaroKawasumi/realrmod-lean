import RMod.BrundanEllis.StackingExternalTensorator
import RMod.BrundanEllis.StackingBiproductTensor
import RMod.Classification.Proofs.ConvolutionInsertions

/-! Fix the full tensor comparison on each convolution summand.  These
identities permit naturality and coherence to be checked on the existing
component comparisons, without changing the chosen finite sums. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace RMod.BrundanEllis.Stacking
open RMod.Classification CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

/-- Expanding the two original convolutions retains their pair of inclusions. -/
theorem exteriorConvolutionExpand_inclusion (s t : Twist) (X X' : pullback s) (Y Y' : pullback t)
    (g a : s.group) (h b : t.group) :
    (convolutionInclusionEven reference.data referenceProperty (oldTwist t).data Y Y' h b ⊗ₘ
      convolutionInclusionEven reference.data referenceProperty (oldTwist s).data X X' g a) ≫
        (exteriorConvolutionExpand s t X X' Y Y' g h).hom =
    biproduct.ι (fun gh : s.group × t.group =>
      convolutionEvenFamily reference.data referenceProperty (oldTwist t).data Y Y' h gh.2 ⊗
        convolutionEvenFamily reference.data referenceProperty (oldTwist s).data X X' g gh.1) (a, b) := by
  letI : Fintype s.group := Fintype.ofFinite _
  letI : Fintype t.group := Fintype.ofFinite _
  let F : t.group → ReferenceEvenCategory reference.data referenceProperty := convolutionEvenFamily reference.data referenceProperty (oldTwist t).data Y Y' h
  let G : s.group → ReferenceEvenCategory reference.data referenceProperty := convolutionEvenFamily reference.data referenceProperty (oldTwist s).data X X' g
  let e := convolutionEvenIso reference.data referenceProperty (oldTwist t).data Y Y' h
  let d := convolutionEvenIso reference.data referenceProperty (oldTwist s).data X X' g
  change ((biproduct.ι F b ≫ e.inv) ⊗ₘ (biproduct.ι G a ≫ d.inv)) ≫
    (tensorIso e d ≪≫ reversedBiproductDistributor F G).hom = _
  rw [Iso.trans_hom, tensorIso_hom, ← Category.assoc, tensorHom_comp_tensorHom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact reversedBiproductDistributor_inclusion F G a b

/-- The inverse expansion recovers the actual chosen convolution inclusions. -/
theorem exteriorConvolutionExpand_inclusion_inv (s t : Twist) (X X' : pullback s) (Y Y' : pullback t)
    (g a : s.group) (h b : t.group) :
    biproduct.ι (fun gh : s.group × t.group =>
      convolutionEvenFamily reference.data referenceProperty (oldTwist t).data Y Y' h gh.2 ⊗
        convolutionEvenFamily reference.data referenceProperty (oldTwist s).data X X' g gh.1) (a, b) ≫
      (exteriorConvolutionExpand s t X X' Y Y' g h).inv =
    convolutionInclusionEven reference.data referenceProperty (oldTwist t).data Y Y' h b ⊗ₘ
      convolutionInclusionEven reference.data referenceProperty (oldTwist s).data X X' g a := by
  apply (cancel_mono (exteriorConvolutionExpand s t X X' Y Y' g h).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, exteriorConvolutionExpand_inclusion]

/-- The assembled even comparison agrees with the prescribed block on each summand. -/
theorem exteriorTensoratorEvenIso_inclusion (s t : Twist) (X X' : pullback s) (Y Y' : pullback t)
    (g a : s.group) (h b : t.group) :
    convolutionInclusionEven reference.data referenceProperty (oldTwist (exteriorTwist s t).val).data
      ((reversedExteriorPairing s t).obj (X, Y)) ((reversedExteriorPairing s t).obj (X', Y')) (g, h) (a, b) ≫
        (exteriorTensoratorEvenIso s t X X' Y Y' g h).hom =
    (exteriorConvolutionBlockIso s t X X' Y Y' g h (a, b)).hom ≫
      (convolutionInclusionEven reference.data referenceProperty (oldTwist t).data Y Y' h b ⊗ₘ
        convolutionInclusionEven reference.data referenceProperty (oldTwist s).data X X' g a) := by
  simp only [convolutionInclusionEven, exteriorTensoratorEvenIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc, biproduct.mapIso_hom, biproduct.ι_map_assoc]
  exact congrArg (fun f => (exteriorConvolutionBlockIso s t X X' Y Y' g h (a, b)).hom ≫ f)
    (exteriorConvolutionExpand_inclusion_inv s t X X' Y Y' g a h b)

/-- The same block formula holds on the full graded Hom carrier. -/
theorem exteriorTensorator_inclusion (s t : Twist) (X X' : pullback s) (Y Y' : pullback t)
    (g a : s.group) (h b : t.group) :
    reference.data.comp
      (convolutionInclusion reference.data referenceProperty (oldTwist (exteriorTwist s t).val).data
        ((reversedExteriorPairing s t).obj (X, Y)) ((reversedExteriorPairing s t).obj (X', Y')) (g, h) (a, b))
      (exteriorTensoratorData s t X X' Y Y' g h).hom =
    reference.data.comp (exteriorBinaryBlockData s t X X' Y Y' a (a⁻¹ * g) b (b⁻¹ * h)).hom
      (reference.data.tensorHom
        (convolutionInclusion reference.data referenceProperty (oldTwist t).data Y Y' h b)
        (convolutionInclusion reference.data referenceProperty (oldTwist s).data X X' g a)) :=
  congrArg (fun f => f.hom) (exteriorTensoratorEvenIso_inclusion s t X X' Y Y' g a h b)

end RMod.BrundanEllis.Stacking
