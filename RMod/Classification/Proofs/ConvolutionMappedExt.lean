import RMod.Classification.Proofs.ConvolutionTripleExt

/-!
# Convolution summand tests after an arbitrary superfunctor

The exact inclusion and projection matrices remain complete after a
linear superfunctor. Applying this to repeated fixed-object tensor
functors lets fourfold diagrams be tested on all of their summands,
without assuming any coherence law in the constructed category.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (D : WeaklyPointedSuperfusion.{u, v})
  (F : Superfunctor ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩ D)

theorem hom_ext_of_mapped_convolutionInclusions (X Y : PullbackObj C t) (k : t.group)
    {M : D.data.Obj} {f g : D.data.Hom (F.data.obj (convolutionObj C hC t X Y k).val) M}
    (he : ∀ a, D.data.comp (F.data.map (convolutionInclusion C hC t X Y k a)) f =
      D.data.comp (F.data.map (convolutionInclusion C hC t X Y k a)) g) : f = g := by
  let d := (convolutionDecomposition C hC t X Y k).map F
  apply hom_ext_of_inclusions D.laws d.data.inclusion d.data.projection d.laws.total
  intro i
  have hi := he (groupEnumeration t i)
  simp only [convolutionInclusion_enumeration] at hi
  exact hi

theorem hom_ext_of_mapped_convolutionLeftInsertions (X Y Z : PullbackObj C t) (k : t.group)
    {M : D.data.Obj}
    {f g : D.data.Hom (F.data.obj (convolutionObj C hC t (convolutionObj C hC t X Y) Z k).val) M}
    (he : ∀ a b,
      D.data.comp (F.data.map (convolutionLeftInsertionEven C hC t X Y Z k a b).hom) f =
        D.data.comp (F.data.map (convolutionLeftInsertionEven C hC t X Y Z k a b).hom) g) : f = g := by
  apply hom_ext_of_mapped_convolutionInclusions C hC t D F (convolutionObj C hC t X Y) Z k
  intro a
  let A : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  let d := (((convolutionDecomposition C hC t X Y a).map
    (tensorRightSuperfunctor A (Z (a⁻¹ * k)).val)).map
      (tensorRightSuperfunctor A (C.pi.factor (t.nu a (a⁻¹ * k))))).map F
  apply hom_ext_of_inclusions D.laws d.data.inclusion d.data.projection d.laws.total
  intro i
  have hi := he a (groupEnumeration t i)
  change D.data.comp (F.data.map (C.comp
    (C.tensorHom (C.tensorHom (convolutionInclusion C hC t X Y a (groupEnumeration t i))
      (C.id (Z (a⁻¹ * k)).val)) (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))
    (convolutionInclusion C hC t (convolutionObj C hC t X Y) Z k a))) f =
    D.data.comp (F.data.map (C.comp
      (C.tensorHom (C.tensorHom (convolutionInclusion C hC t X Y a (groupEnumeration t i))
        (C.id (Z (a⁻¹ * k)).val)) (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))
      (convolutionInclusion C hC t (convolutionObj C hC t X Y) Z k a))) g at hi
  simp only [F.laws.map_comp, convolutionInclusion_enumeration, D.laws.comp_assoc] at hi
  exact hi

theorem hom_ext_of_mapped_convolutionRightInsertions (X Y Z : PullbackObj C t) (k : t.group)
    {M : D.data.Obj}
    {f g : D.data.Hom (F.data.obj (convolutionObj C hC t X (convolutionObj C hC t Y Z) k).val) M}
    (he : ∀ a b,
      D.data.comp (F.data.map (convolutionRightInsertionEven C hC t X Y Z k a b).hom) f =
        D.data.comp (F.data.map (convolutionRightInsertionEven C hC t X Y Z k a b).hom) g) : f = g := by
  apply hom_ext_of_mapped_convolutionInclusions C hC t D F X (convolutionObj C hC t Y Z) k
  intro a
  let A : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  let d := (((convolutionDecomposition C hC t Y Z (a⁻¹ * k)).map
    (tensorLeftSuperfunctor A (X a).val)).map
      (tensorRightSuperfunctor A (C.pi.factor (t.nu a (a⁻¹ * k))))).map F
  apply hom_ext_of_inclusions D.laws d.data.inclusion d.data.projection d.laws.total
  intro i
  have hi := he a (groupEnumeration t i)
  change D.data.comp (F.data.map (C.comp
    (C.tensorHom (C.tensorHom (C.id (X a).val)
      (convolutionInclusion C hC t Y Z (a⁻¹ * k) (groupEnumeration t i)))
      (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))
    (convolutionInclusion C hC t X (convolutionObj C hC t Y Z) k a))) f =
    D.data.comp (F.data.map (C.comp
      (C.tensorHom (C.tensorHom (C.id (X a).val)
        (convolutionInclusion C hC t Y Z (a⁻¹ * k) (groupEnumeration t i)))
        (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))
      (convolutionInclusion C hC t X (convolutionObj C hC t Y Z) k a))) g at hi
  simp only [F.laws.map_comp, convolutionInclusion_enumeration, D.laws.comp_assoc] at hi
  exact hi

end RMod.Classification
