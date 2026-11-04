import RMod.Classification.Instances.ConvolutionTripleInsertions
import RMod.Classification.Proofs.ConvolutionInsertions
import RMod.Classification.Instances.DecompositionMap
import RMod.Classification.Instances.TensorFunctors

/-!
# Threefold summand tests on full graded Hom spaces

The outer convolution inclusion detects equality. Tensoring the chosen
inner decomposition by the remaining objects preserves its complete
matrix identities, because fixed-object tensoring is a superfunctor.
This proves the two triple-summand tests even for inhomogeneous maps.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

theorem hom_ext_of_convolutionLeftInsertions (X Y Z : PullbackObj C t) (k : t.group)
    {M : C.Obj} {f g : C.Hom (convolutionObj C hC t (convolutionObj C hC t X Y) Z k).val M}
    (he : ∀ a b, C.comp (convolutionLeftInsertionEven C hC t X Y Z k a b).hom f =
      C.comp (convolutionLeftInsertionEven C hC t X Y Z k a b).hom g) : f = g := by
  apply hom_ext_of_convolutionInclusions C hC t (convolutionObj C hC t X Y) Z k
  intro a
  let A : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  let d := ((convolutionDecomposition C hC t X Y a).map
    (tensorRightSuperfunctor A (Z (a⁻¹ * k)).val)).map
      (tensorRightSuperfunctor A (C.pi.factor (t.nu a (a⁻¹ * k))))
  apply hom_ext_of_inclusions hC.toWeaklyPointedSuperfusionLaws d.data.inclusion d.data.projection d.laws.total
  intro i
  have hi := he a (groupEnumeration t i)
  change C.comp (C.comp
    (C.tensorHom (C.tensorHom (convolutionInclusion C hC t X Y a (groupEnumeration t i))
      (C.id (Z (a⁻¹ * k)).val)) (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))
    (convolutionInclusion C hC t (convolutionObj C hC t X Y) Z k a)) f =
    C.comp (C.comp
      (C.tensorHom (C.tensorHom (convolutionInclusion C hC t X Y a (groupEnumeration t i))
        (C.id (Z (a⁻¹ * k)).val)) (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))
      (convolutionInclusion C hC t (convolutionObj C hC t X Y) Z k a)) g at hi
  simp only [convolutionInclusion_enumeration, hC.comp_assoc] at hi
  exact hi

theorem hom_ext_of_convolutionRightInsertions (X Y Z : PullbackObj C t) (k : t.group)
    {M : C.Obj} {f g : C.Hom (convolutionObj C hC t X (convolutionObj C hC t Y Z) k).val M}
    (he : ∀ a b, C.comp (convolutionRightInsertionEven C hC t X Y Z k a b).hom f =
      C.comp (convolutionRightInsertionEven C hC t X Y Z k a b).hom g) : f = g := by
  apply hom_ext_of_convolutionInclusions C hC t X (convolutionObj C hC t Y Z) k
  intro a
  let A : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  let d := ((convolutionDecomposition C hC t Y Z (a⁻¹ * k)).map
    (tensorLeftSuperfunctor A (X a).val)).map
      (tensorRightSuperfunctor A (C.pi.factor (t.nu a (a⁻¹ * k))))
  apply hom_ext_of_inclusions hC.toWeaklyPointedSuperfusionLaws d.data.inclusion d.data.projection d.laws.total
  intro i
  have hi := he a (groupEnumeration t i)
  change C.comp (C.comp
    (C.tensorHom (C.tensorHom (C.id (X a).val)
      (convolutionInclusion C hC t Y Z (a⁻¹ * k) (groupEnumeration t i)))
      (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))
    (convolutionInclusion C hC t X (convolutionObj C hC t Y Z) k a)) f =
    C.comp (C.comp
      (C.tensorHom (C.tensorHom (C.id (X a).val)
        (convolutionInclusion C hC t Y Z (a⁻¹ * k) (groupEnumeration t i)))
        (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))
      (convolutionInclusion C hC t X (convolutionObj C hC t Y Z) k a)) g at hi
  simp only [convolutionInclusion_enumeration, hC.comp_assoc] at hi
  exact hi

end RMod.Classification
