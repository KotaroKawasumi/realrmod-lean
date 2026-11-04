import RMod.Classification.Proofs.GaugeIndexedLeftRatio
import RMod.Classification.Proofs.GaugeIndexedRightRatio
import RMod.Classification.Proofs.ScalarFaithfulness
import RMod.Classification.Proofs.TensorNonvanishing

/-!
# Faithful scalar comparison on the actual triple evaluation

Each binary evaluation is an isomorphism on its component. Hence the
left triple evaluation is nonzero on three nonzero coordinates. Comparing
the two transported routes then gives an equality of real coefficients,
using the source and target associators already constructed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (twistedPullback C hC t).toWeaklyPointedSuperfusion)
  (g h k u v w : s.data.group)
  (eu : g * h = u) (ev : h * k = v) (ew : u * k = w) (ew' : g * v = w)
  (X : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (pullbackDegreeSimple C hC s g).data.object)
  (Y : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (pullbackDegreeSimple C hC s h).data.object)
  (Z : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (pullbackDegreeSimple C hC s k).data.object)

theorem convolutionIndexedLeftComparison_nonzero
    (hX : C.id (X.obj g).val ≠ C.zero) (hY : C.id (Y.obj h).val ≠ C.zero)
    (hZ : C.id (Z.obj k).val ≠ C.zero) :
    (convolutionIndexedLeftComparisonData C hC s.data X.obj Y.obj Z.obj g h k u w eu ew).hom ≠ C.zero := by
  let P := pullbackIndexedTensorSpanObj C hC s g h u eu X Y
  have hi := (convolutionIndexedComparison_homogeneousIso C hC s.data P.obj Z.obj u k w ew
    (pullback_named_span_supported C hC s u P)).trans hC.toWeaklyPointedSuperfusionLaws
      ((convolutionIndexedComparison_homogeneousIso C hC s.data X.obj Y.obj g h u eu
        (pullback_named_span_supported C hC s g X)).whiskerRight hC.toWeaklyPointedSuperfusionLaws (Z.obj k).val)
  have hn := tensor_id_ne_zero (C := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩)
    (tensor_id_ne_zero (C := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩) hX hY) hZ
  intro hz
  apply hn
  exact hi.inv_hom.symm.trans ((congrArg (C.comp _) hz).trans (raw_comp_zero hC.toWeaklyPointedSuperfusionLaws _))

include eu ev ew ew' in
theorem equivalenceIndexedComparison_scalar_coherence
    (hX : C.id (X.obj g).val ≠ C.zero) (hY : C.id (Y.obj h).val ≠ C.zero)
    (hZ : C.id (Z.obj k).val ≠ C.zero) :
    let phi := equivalenceGaugePhi C hC s t E
    ((t.data.omega (phi g) (phi h) (phi k)).val * (-1 : ℝ) ^
      (t.data.nu (phi g) (phi h) * t.data.nu (phi u) (phi k) +
        t.data.nu (phi h) (phi k) * t.data.nu (phi g) (phi v)).val) *
      ((equivalenceGaugeRatio C hC s t E u k).val * (equivalenceGaugeRatio C hC s t E g h).val *
        (-1 : ℝ) ^ (equivalenceGaugeLambda C hC s t E k * t.data.nu (phi g) (phi h)).val) =
    ((equivalenceGaugeRatio C hC s t E g v).val * (equivalenceGaugeRatio C hC s t E h k).val *
        (-1 : ℝ) ^ (equivalenceGaugeLambda C hC s t E g * s.data.nu h k).val) *
      ((s.data.omega g h k).val * (-1 : ℝ) ^ (s.data.nu g h * s.data.nu u k + s.data.nu h k * s.data.nu g v).val) := by
  have ep : s.data.nu g h + s.data.nu u k = s.data.nu h k + s.data.nu g v := by
    simpa only [← eu, ← ev] using s.laws.normalizer_parity g h k
  have hs := convolutionIndexedComparison_associator C hC s.data s.laws.normalizer_parity
    X.obj Y.obj Z.obj g h k u v w w eu ev ew ew' rfl ep
    (pullback_named_span_supported C hC s g X) (pullback_named_span_supported C hC s h Y)
  simp only [IsoData.ofEq, IsoData.refl, hC.comp_id] at hs
  have he := equivalenceIndexedTransport_target_associator C hC s t E g h k u v w eu ev ew ew' X Y Z
  rw [equivalenceIndexedLeftTransport_ratio, equivalenceIndexedRightTransport_ratio] at he
  have hr := congrArg (C.smul ((equivalenceGaugeRatio C hC s t E g v).val *
    (equivalenceGaugeRatio C hC s t E h k).val * (-1 : ℝ) ^
      (equivalenceGaugeLambda C hC s t E g * s.data.nu h k).val)) hs
  have hh := he.symm.trans hr
  simp only [← hC.mul_smul] at hh
  exact raw_smul_injective ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩ _
    (convolutionIndexedLeftComparison_nonzero C hC s g h k u w eu ew X Y Z hX hY hZ) hh

end RMod.Classification
