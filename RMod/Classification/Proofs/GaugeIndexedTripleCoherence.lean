import RMod.Classification.Instances.GaugeIndexedTripleTransport
import RMod.Classification.Proofs.GaugeIndexedComparisonLaws
import RMod.Classification.Proofs.EquivalenceRawAssociativity
import RMod.Classification.Proofs.IsoNaturality

/-!
# Coherence of the transported triple routes

The target route equation is the given monoidal equivalence's coherence,
conjugated by the same chosen input and output comparisons. Naturality of
the output comparison moves the source associator through its inverse.
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

theorem equivalenceIndexedTransport_target_associator :
    (equivalenceIndexedRightTransportData C hC s t E g h k X Y Z u v w eu ev ew ew').hom =
      C.smul ((t.data.omega (equivalenceGaugePhi C hC s t E g)
        (equivalenceGaugePhi C hC s t E h) (equivalenceGaugePhi C hC s t E k)).val *
        (-1 : ℝ) ^ (t.data.nu (equivalenceGaugePhi C hC s t E g) (equivalenceGaugePhi C hC s t E h) *
          t.data.nu (equivalenceGaugePhi C hC s t E u) (equivalenceGaugePhi C hC s t E k) +
          t.data.nu (equivalenceGaugePhi C hC s t E h) (equivalenceGaugePhi C hC s t E k) *
          t.data.nu (equivalenceGaugePhi C hC s t E g) (equivalenceGaugePhi C hC s t E v)).val)
        (equivalenceIndexedLeftTransportData C hC s t E g h k X Y Z u w eu ew).hom := by
  let phi := equivalenceGaugePhi C hC s t E
  have ep : t.data.nu (phi g) (phi h) + t.data.nu (phi u) (phi k) =
      t.data.nu (phi h) (phi k) + t.data.nu (phi g) (phi v) := by
    simpa only [← eu, ← ev, map_mul] using t.laws.normalizer_parity (phi g) (phi h) (phi k)
  have he := equivalenceIndexedComparison_associator C hC s t E X.obj Y.obj Z.obj
    (phi g) (phi h) (phi k) (phi u) (phi v) (phi w)
    ((map_mul phi g h).symm.trans (congrArg phi eu))
    ((map_mul phi h k).symm.trans (congrArg phi ev))
    ((map_mul phi u k).symm.trans (congrArg phi ew))
    ((map_mul phi g v).symm.trans (congrArg phi ew')) ep
    (equivalence_named_span_supported C hC s t E g X)
    (equivalence_named_span_supported C hC s t E h Y)
  let o := (equivalenceNamedComparisonData C hC s t E w
    (pullbackIndexedTensorSpanObj C hC s u k w ew
      (pullbackIndexedTensorSpanObj C hC s g h u eu X Y) Z)).inv
  let j := (equivalenceNamedTripleInputComparisonData C hC s t E g h k X Y Z).hom
  have hh := congrArg (fun q => C.comp (C.comp o q) j) he
  simpa only [equivalenceIndexedRightTransportData, equivalenceIndexedLeftTransportData,
    IsoData.trans, IsoData.symm, hC.comp_assoc, hC.comp_smul, hC.smul_comp] using hh

theorem equivalenceNamedComparison_inv_associator :
    C.comp (equivalenceNamedComparisonData C hC s t E w
      (pullbackIndexedTensorSpanObj C hC s u k w ew
        (pullbackIndexedTensorSpanObj C hC s g h u eu X Y) Z)).inv
      (E.data.forward.map ((twistedPullback C hC s).data.associatorHom X.obj Y.obj Z.obj)
        (equivalenceGaugePhi C hC s t E w)) =
    C.comp ((twistedPullback C hC s).data.associatorHom X.obj Y.obj Z.obj w)
      (equivalenceNamedComparisonData C hC s t E w
        (pullbackIndexedTensorSpanObj C hC s g v w ew' X
          (pullbackIndexedTensorSpanObj C hC s h k v ev Y Z))).inv := by
  let L := pullbackIndexedTensorSpanObj C hC s u k w ew
    (pullbackIndexedTensorSpanObj C hC s g h u eu X Y) Z
  let R := pullbackIndexedTensorSpanObj C hC s g v w ew' X
    (pullbackIndexedTensorSpanObj C hC s h k v ev Y Z)
  let f : L ⟶ R := ⟨(twistedPullback C hC s).data.associatorHom X.obj Y.obj Z.obj⟩
  have hn := equivalenceNamedComparison_naturality C hC s t E w f
    ((twistedPullback C hC s).laws.associator_hom_even X.obj Y.obj Z.obj)
  simp only [mul_zero, ZMod.val_zero, pow_zero, hC.one_smul] at hn
  exact (iso_naturality_symm hC.toWeaklyPointedSuperfusionLaws
    (equivalenceNamedComparison_homogeneousIso C hC s t E w L).toIsoLaws
    (equivalenceNamedComparison_homogeneousIso C hC s t E w R).toIsoLaws hn).symm

end RMod.Classification
