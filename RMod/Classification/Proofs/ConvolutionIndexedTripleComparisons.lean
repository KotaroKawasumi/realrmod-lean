import RMod.Classification.Instances.ConvolutionIndexedTripleComparisons
import RMod.Classification.Proofs.ConvolutionIndexedComparisons
import RMod.Classification.Proofs.OuterParityDeletion

/-!
# Raw triple evaluation on the original convolution summands

The binary inclusion-comparison identities remove both summand maps.
Naturality of parity deletion moves the remaining even inclusion past
the outer deletion. Thus the resulting maps are precisely the two
outer-first deletion routes, with no unspecified scalar.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace RMod.Classification

attribute [local implicit_reducible] twistSummand

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

theorem convolutionIndexedLeftComparison_inclusion (X Y Z : PullbackObj C t)
    (g h k u w : t.group) (eu : g * h = u) (ew : u * k = w) :
    C.comp (convolutionIndexedLeftInsertion C hC t X Y Z g h k u w eu ew)
      (convolutionIndexedLeftComparisonData C hC t X Y Z g h k u w eu ew).hom =
      C.comp (C.pi.rightFactorDeletion (C.tensorObj (twistSummand C t X Y g h) (Z k).val)
        (t.nu u k)).hom
        (C.tensorHom (C.pi.rightFactorDeletion (C.tensorObj (X g).val (Y h).val) (t.nu g h)).hom
          (C.id (Z k).val)) := by
  let i := convolutionIndexedProductInclusion C hC t X Y g h u eu
  let j := convolutionIndexedProductInclusion C hC t (convolutionObj C hC t X Y) Z u k w ew
  let b := convolutionIndexedComparisonData C hC t X Y g h u eu
  let q := convolutionIndexedComparisonData C hC t (convolutionObj C hC t X Y) Z u k w ew
  have hn := hC.pi.rightFactorDeletion_naturality hC.toWeaklyPointedSuperfusionLaws (t.nu u k)
    (C.tensorHom i (C.id (Z k).val))
    (tensor_even hC.toWeaklyPointedSuperfusionLaws
      (convolutionIndexedInclusion_grade C hC t X Y g h u eu) (hC.id_even (Z k).val))
  simp only [mul_zero, ZMod.val_zero, pow_zero, hC.one_smul] at hn
  change C.comp (C.comp (C.tensorHom (C.tensorHom i (C.id (Z k).val))
    (C.id (C.pi.factor (t.nu u k)))) j) (C.comp q.hom (C.tensorHom b.hom (C.id (Z k).val))) = _
  rw [hC.comp_assoc, ← hC.comp_assoc j q.hom,
    convolutionIndexedComparison_inclusion C hC t (convolutionObj C hC t X Y) Z u k w ew,
    ← hC.comp_assoc, hn, hC.comp_assoc,
    interchange_second_even hC.toWeaklyPointedSuperfusionLaws _ _ _ _ (hC.id_even (Z k).val),
    hC.id_comp, convolutionIndexedComparison_inclusion C hC t X Y g h u eu]

theorem convolutionIndexedRightComparison_inclusion (X Y Z : PullbackObj C t)
    (g h k v w : t.group) (ev : h * k = v) (ew : g * v = w) :
    C.comp (convolutionIndexedRightInsertion C hC t X Y Z g h k v w ev ew)
      (convolutionIndexedRightComparisonData C hC t X Y Z g h k v w ev ew).hom =
      C.comp (C.pi.rightFactorDeletion (C.tensorObj (X g).val (twistSummand C t Y Z h k))
        (t.nu g v)).hom
        (C.comp (C.tensorHom (C.id (X g).val)
          (C.pi.rightFactorDeletion (C.tensorObj (Y h).val (Z k).val) (t.nu h k)).hom)
          (C.associatorInv (X g).val (Y h).val (Z k).val)) := by
  let i := convolutionIndexedProductInclusion C hC t Y Z h k v ev
  let j := convolutionIndexedProductInclusion C hC t X (convolutionObj C hC t Y Z) g v w ew
  let b := convolutionIndexedComparisonData C hC t Y Z h k v ev
  let q := convolutionIndexedComparisonData C hC t X (convolutionObj C hC t Y Z) g v w ew
  have hn := hC.pi.rightFactorDeletion_naturality hC.toWeaklyPointedSuperfusionLaws (t.nu g v)
    (C.tensorHom (C.id (X g).val) i)
    (tensor_even hC.toWeaklyPointedSuperfusionLaws (hC.id_even (X g).val)
      (convolutionIndexedInclusion_grade C hC t Y Z h k v ev))
  simp only [mul_zero, ZMod.val_zero, pow_zero, hC.one_smul] at hn
  change C.comp (C.comp (C.tensorHom (C.tensorHom (C.id (X g).val) i)
    (C.id (C.pi.factor (t.nu g v)))) j)
    (C.comp (C.comp q.hom (C.tensorHom (C.id (X g).val) b.hom))
      (C.associatorInv (X g).val (Y h).val (Z k).val)) = _
  rw [hC.comp_assoc q.hom, hC.comp_assoc, ← hC.comp_assoc j q.hom,
    convolutionIndexedComparison_inclusion C hC t X (convolutionObj C hC t Y Z) g v w ew,
    ← hC.comp_assoc, hn, hC.comp_assoc, ← hC.comp_assoc (C.tensorHom (C.id (X g).val) i),
    interchange_first_even hC.toWeaklyPointedSuperfusionLaws _ _ _ _ (hC.id_even (X g).val),
    hC.id_comp, convolutionIndexedComparison_inclusion C hC t Y Z h k v ev]

end RMod.Classification
