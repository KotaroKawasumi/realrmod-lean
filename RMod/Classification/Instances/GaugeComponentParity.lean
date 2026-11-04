import RMod.Classification.Instances.EquivalenceReferenceComponent
import RMod.Classification.Proofs.ComponentComparisonLines

/-!
# The component parity extracted from an arbitrary model equivalence

Compare the induced reference-component autoequivalence with the identity.
The comparison-line theorem supplies one and only one parity. Select that
parity and the actual invertible signed-natural comparison; its maps and
the laws of those exact maps are retained separately. Normalization at the
identity and compatibility with tensor products are subsequent theorems.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (twistedPullback C hC t).toWeaklyPointedSuperfusion)

noncomputable def equivalenceReferenceIdentity (g : s.data.group) :
    SpanSuperequivalence
      ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
      ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
      ((pullbackDegreeSimple C hC s g).data.object
        (pullbackSimpleDegree C hC s (pullbackDegreeSimple C hC s g))).val
      ((pullbackDegreeSimple C hC s g).data.object
        (pullbackSimpleDegree C hC s (pullbackDegreeSimple C hC s g))).val :=
  spanChangeSuperequivalence ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
    (fun _ => Iff.rfl)

theorem exists_unique_equivalenceComponentParity (g : s.data.group) :
    ∃! a : ZMod 2, Nonempty (SpanHomogeneousNatIso
      (equivalenceReferenceComponent C hC s t E (pullbackDegreeSimple C hC s g)).forwardFunctor
      (equivalenceReferenceIdentity C hC s g).forwardFunctor a) :=
  exists_unique_spanNaturalIso_parity
    (pullbackSimpleDegree_simple C hC s (pullbackDegreeSimple C hC s g))
    (pullbackSimpleDegree_simple C hC s (pullbackDegreeSimple C hC s g))
    (equivalenceReferenceComponent C hC s t E (pullbackDegreeSimple C hC s g))
    (equivalenceReferenceIdentity C hC s g)

noncomputable def equivalenceGaugeLambda (g : s.data.group) : ZMod 2 :=
  (exists_unique_equivalenceComponentParity C hC s t E g).choose

noncomputable def equivalenceReferenceComparisonData (g : s.data.group) :
    SpanHomogeneousNatIsoData
      (equivalenceReferenceComponent C hC s t E (pullbackDegreeSimple C hC s g)).forwardFunctor.data
      (equivalenceReferenceIdentity C hC s g).forwardFunctor.data :=
  (Classical.choice (exists_unique_equivalenceComponentParity C hC s t E g).choose_spec.1).data

theorem equivalenceReferenceComparisonLaws (g : s.data.group) :
    SpanHomogeneousNatIsoLaws (equivalenceGaugeLambda C hC s t E g)
      (equivalenceReferenceComparisonData C hC s t E g) :=
  (Classical.choice (exists_unique_equivalenceComponentParity C hC s t E g).choose_spec.1).laws

noncomputable def equivalenceReferenceComparison (g : s.data.group) :
    SpanHomogeneousNatIso
      (equivalenceReferenceComponent C hC s t E (pullbackDegreeSimple C hC s g)).forwardFunctor
      (equivalenceReferenceIdentity C hC s g).forwardFunctor (equivalenceGaugeLambda C hC s t E g) :=
  ⟨equivalenceReferenceComparisonData C hC s t E g, equivalenceReferenceComparisonLaws C hC s t E g⟩

theorem equivalenceGaugeLambda_unique (g : s.data.group) (a : ZMod 2)
    (ha : Nonempty (SpanHomogeneousNatIso
      (equivalenceReferenceComponent C hC s t E (pullbackDegreeSimple C hC s g)).forwardFunctor
      (equivalenceReferenceIdentity C hC s g).forwardFunctor a)) :
    a = equivalenceGaugeLambda C hC s t E g :=
  (exists_unique_equivalenceComponentParity C hC s t E g).choose_spec.2 a ha

end RMod.Classification
