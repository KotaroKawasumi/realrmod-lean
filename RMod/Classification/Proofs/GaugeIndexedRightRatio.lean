import RMod.Classification.Proofs.GaugeIndexedTripleCoherence
import RMod.Classification.Proofs.TensorComparisonRatioComposition

/-!
# The extracted binary ratios on the right triple route

Naturality moves the output comparison across the source associator.
Cancellation of the intermediate comparison leaves the crossing of the
first component parity with the changed inner comparison. The ordinary
associator is retained until the two evaluations have the same target.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace RMod.Classification

open CategoryTheory

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

theorem equivalenceIndexedRightTransport_ratio :
    (equivalenceIndexedRightTransportData C hC s t E g h k X Y Z u v w eu ev ew ew').hom =
      C.smul ((equivalenceGaugeRatio C hC s t E g v).val *
        (equivalenceGaugeRatio C hC s t E h k).val * (-1 : ℝ) ^
          (equivalenceGaugeLambda C hC s t E g * s.data.nu h k).val)
        (C.comp ((twistedPullback C hC s).data.associatorHom X.obj Y.obj Z.obj w)
          (convolutionIndexedRightComparisonData C hC s.data X.obj Y.obj Z.obj g h k v w ev ew').hom) := by
  let phi := equivalenceGaugePhi C hC s t E
  let P := pullbackIndexedTensorSpanObj C hC s h k v ev Y Z
  let Q := pullbackIndexedTensorSpanObj C hC s g v w ew' X P
  let i := (equivalenceNamedComparisonData C hC s t E g X).hom
  let j := equivalenceNamedComparisonData C hC s t E v P
  let a := (equivalenceIndexedComparisonData C hC s t E Y.obj Z.obj (phi h) (phi k) (phi v)
    ((map_mul phi h k).symm.trans (congrArg phi ev))).hom
  let l := C.tensorHom (equivalenceNamedComparisonData C hC s t E h Y).hom
    (equivalenceNamedComparisonData C hC s t E k Z).hom
  let o := (equivalenceNamedComparisonData C hC s t E w Q).inv
  let p := (equivalenceIndexedComparisonData C hC s t E X.obj P.obj (phi g) (phi v) (phi w)
    ((map_mul phi g v).symm.trans (congrArg phi ew'))).hom
  let q := (convolutionIndexedComparisonData C hC s.data Y.obj Z.obj h k v ev).hom
  let r := (convolutionIndexedComparisonData C hC s.data X.obj P.obj g v w ew').hom
  have h₁ : C.comp j.inv (C.comp a l) = C.smul (equivalenceGaugeRatio C hC s t E h k).val q :=
    (hC.comp_assoc _ _ _).symm.trans (equivalenceIndexedComparison_ratio C hC s t E h k v ev Y Z)
  have h₂ : C.comp (C.comp o p) (C.tensorHom i j.hom) =
      C.smul (equivalenceGaugeRatio C hC s t E g v).val r :=
    equivalenceIndexedComparison_ratio C hC s t E g v w ew' X P
  have ha : C.IsHomogeneous (s.data.nu h k) (C.comp j.inv (C.comp a l)) := by
    rw [← hC.comp_assoc]
    exact equivalenceIndexedChangedComparison_hom_grade C hC s t E h k v ev Y Z
  have he := tensorComparisonRatio_right hC.toWeaklyPointedSuperfusionLaws i j
    (equivalenceNamedComparison_homogeneousIso C hC s t E v P).toIsoLaws a l o p q r
    (equivalenceGaugeRatio C hC s t E h k).val (equivalenceGaugeRatio C hC s t E g v).val
    (equivalenceNamedComparison_homogeneousIso C hC s t E g X).hom_grade ha h₁ h₂
  let z := (equivalenceNamedTripleInputComparisonData C hC s t E g h k X Y Z).hom
  let ae := C.associatorInv (E.data.forward.obj X.obj (phi g)).val
    (E.data.forward.obj Y.obj (phi h)).val (E.data.forward.obj Z.obj (phi k)).val
  let as := C.associatorInv (X.obj g).val (Y.obj h).val (Z.obj k).val
  have hn : C.comp ae z = C.comp (C.tensorHom i l) as :=
    (iso_naturality_symm hC.toWeaklyPointedSuperfusionLaws
      (EvenIsoLaws.assoc hC.toWeaklyPointedSuperfusionLaws
        (E.data.forward.obj X.obj (phi g)).val (E.data.forward.obj Y.obj (phi h)).val
        (E.data.forward.obj Z.obj (phi k)).val).toIsoLaws
      (EvenIsoLaws.assoc hC.toWeaklyPointedSuperfusionLaws
        (X.obj g).val (Y.obj h).val (Z.obj k).val).toIsoLaws
      (hC.associator_naturality i (equivalenceNamedComparisonData C hC s t E h Y).hom
        (equivalenceNamedComparisonData C hC s t E k Z).hom)).symm
  have hb : C.comp (C.comp o (equivalenceIndexedRightComparisonData C hC s t E X.obj Y.obj Z.obj
        (phi g) (phi h) (phi k) (phi v) (phi w)
        ((map_mul phi h k).symm.trans (congrArg phi ev))
        ((map_mul phi g v).symm.trans (congrArg phi ew'))).hom) z =
      C.smul ((equivalenceGaugeRatio C hC s t E g v).val *
        (equivalenceGaugeRatio C hC s t E h k).val * (-1 : ℝ) ^
          (equivalenceGaugeLambda C hC s t E g * s.data.nu h k).val)
        (convolutionIndexedRightComparisonData C hC s.data X.obj Y.obj Z.obj g h k v w ev ew').hom := by
    change C.comp (C.comp o (C.comp (C.comp p
      (C.tensorHom (C.id (E.data.forward.obj X.obj (phi g)).val) a)) ae)) z =
      C.smul _ (C.comp (C.comp r (C.tensorHom (C.id (X.obj g).val) q)) as)
    rw [hC.comp_assoc o, hC.comp_assoc _ ae, hn]
    have hh := congrArg (fun b => C.comp b as) he
    simpa only [hC.comp_assoc, hC.smul_comp] using hh
  have ho := equivalenceNamedComparison_inv_associator C hC s t E g h k u v w eu ev ew ew' X Y Z
  dsimp only [equivalenceIndexedRightTransportData, IsoData.trans, IsoData.symm]
  rw [ho, hC.comp_assoc, hC.comp_assoc]
  have hh := congrArg (C.comp ((twistedPullback C hC s).data.associatorHom X.obj Y.obj Z.obj w)) hb
  simpa only [hC.comp_assoc, hC.comp_smul] using hh

end RMod.Classification
