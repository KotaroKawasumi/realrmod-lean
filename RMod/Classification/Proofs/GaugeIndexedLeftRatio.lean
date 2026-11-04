import RMod.Classification.Instances.GaugeIndexedTripleTransport
import RMod.Classification.Proofs.GaugeIndexedComparisonLaws
import RMod.Classification.Proofs.TensorComparisonRatioComposition

/-!
# The two extracted binary ratios on the left triple route

Use the same selected comparison on the intermediate product component.
Its inverse cancels, leaving the crossing of the third component parity
with the original target binary comparison. The coefficient multiplies
the actual source triple evaluation on arbitrary component objects.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace RMod.Classification

theorem equivalenceIndexedLeftTransport_ratio
    (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
    (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (twistedPullback C hC t).toWeaklyPointedSuperfusion)
    (g h k u w : s.data.group) (eu : g * h = u) (ew : u * k = w)
    (X : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s g).data.object)
    (Y : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s h).data.object)
    (Z : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s k).data.object) :
    (equivalenceIndexedLeftTransportData C hC s t E g h k X Y Z u w eu ew).hom =
      C.smul ((equivalenceGaugeRatio C hC s t E u k).val *
        (equivalenceGaugeRatio C hC s t E g h).val * (-1 : ℝ) ^
          (equivalenceGaugeLambda C hC s t E k *
            t.data.nu (equivalenceGaugePhi C hC s t E g) (equivalenceGaugePhi C hC s t E h)).val)
        (convolutionIndexedLeftComparisonData C hC s.data X.obj Y.obj Z.obj g h k u w eu ew).hom := by
  let phi := equivalenceGaugePhi C hC s t E
  let P := pullbackIndexedTensorSpanObj C hC s g h u eu X Y
  let Q := pullbackIndexedTensorSpanObj C hC s u k w ew P Z
  let i := equivalenceNamedComparisonData C hC s t E u P
  let j := (equivalenceNamedComparisonData C hC s t E k Z).hom
  let a := (equivalenceIndexedComparisonData C hC s t E X.obj Y.obj (phi g) (phi h) (phi u)
    ((map_mul phi g h).symm.trans (congrArg phi eu))).hom
  let l := C.tensorHom (equivalenceNamedComparisonData C hC s t E g X).hom
    (equivalenceNamedComparisonData C hC s t E h Y).hom
  let o := (equivalenceNamedComparisonData C hC s t E w Q).inv
  let p := (equivalenceIndexedComparisonData C hC s t E P.obj Z.obj (phi u) (phi k) (phi w)
    ((map_mul phi u k).symm.trans (congrArg phi ew))).hom
  let q := (convolutionIndexedComparisonData C hC s.data X.obj Y.obj g h u eu).hom
  let r := (convolutionIndexedComparisonData C hC s.data P.obj Z.obj u k w ew).hom
  have h₁ : C.comp i.inv (C.comp a l) = C.smul (equivalenceGaugeRatio C hC s t E g h).val q :=
    (hC.comp_assoc _ _ _).symm.trans (equivalenceIndexedComparison_ratio C hC s t E g h u eu X Y)
  have h₂ : C.comp (C.comp o p) (C.tensorHom i.hom j) =
      C.smul (equivalenceGaugeRatio C hC s t E u k).val r :=
    equivalenceIndexedComparison_ratio C hC s t E u k w ew P Z
  have he := tensorComparisonRatio_left hC.toWeaklyPointedSuperfusionLaws i
    (equivalenceNamedComparison_homogeneousIso C hC s t E u P).toIsoLaws j a l o p q r
    (equivalenceGaugeRatio C hC s t E g h).val (equivalenceGaugeRatio C hC s t E u k).val
    (equivalenceNamedComparison_homogeneousIso C hC s t E k Z).hom_grade
    (equivalenceIndexedComponentComparison_homogeneousIso C hC s t E g h u eu X Y).hom_grade h₁ h₂
  change C.comp (C.comp o (C.comp p (C.tensorHom a (C.id (E.data.forward.obj Z.obj (phi k)).val))))
    (C.tensorHom l j) = C.smul _ (C.comp r (C.tensorHom q (C.id (Z.obj k).val)))
  simpa only [hC.comp_assoc] using he

end RMod.Classification
