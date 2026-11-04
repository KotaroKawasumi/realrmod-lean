import RMod.Classification.Instances.TwistedPullback
import RMod.Classification.Instances.ReferenceSimpleRepresentatives
import RMod.Classification.Proofs.PullbackOrbitSupport

/-!
# Group labels and selected simple objects in a pullback model

A simple object's unique nonzero support supplies its actual group label.
Conversely, place the reference's selected simple of type rho(g) at g.
The selected object data and their simplicity laws are bundled only after
proving the latter for those exact data.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : Twist)

noncomputable def pullbackSimpleDegree
    (X : SimpleObject (twistedPullback C hC t).toWeaklyPointedSuperfusion) : t.data.group :=
  (twistedPullback_simple_support C hC t.data t.laws X.data.object X.laws.simple).choose

theorem pullbackSimpleDegree_supported
    (X : SimpleObject (twistedPullback C hC t).toWeaklyPointedSuperfusion) :
    ∀ k, k ≠ pullbackSimpleDegree C hC t X → C.id (X.data.object k).val = C.zero :=
  (twistedPullback_simple_support C hC t.data t.laws X.data.object X.laws.simple).choose_spec.1

theorem pullbackSimpleDegree_simple
    (X : SimpleObject (twistedPullback C hC t).toWeaklyPointedSuperfusion) :
    C.IsSimple (X.data.object (pullbackSimpleDegree C hC t X)).val :=
  (twistedPullback_simple_support C hC t.data t.laws X.data.object X.laws.simple).choose_spec.2

noncomputable def pullbackDegreeSimpleData (g : t.data.group) :
    SimpleObjectData (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData :=
  let C₀ : PiSuperfusion := ⟨C, hC.toPiSuperfusionLaws⟩
  let S := referenceSimpleRepresentative C₀ hC (Multiplicative.toAdd (t.data.rho g))
  ⟨placedObj C hC t.data g S.data.object
    (InComponent.of_simple hC S.laws.simple (referenceSimpleRepresentative_type C₀ hC _))⟩

theorem pullbackDegreeSimpleLaws (g : t.data.group) :
    SimpleObjectLaws (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData
      (pullbackDegreeSimpleData C hC t g) :=
  ⟨twistedPullback_placed_simple C hC t.data t.laws g _
    (InComponent.of_simple hC
      (referenceSimpleRepresentative ⟨C, hC.toPiSuperfusionLaws⟩ hC
        (Multiplicative.toAdd (t.data.rho g))).laws.simple
      (referenceSimpleRepresentative_type ⟨C, hC.toPiSuperfusionLaws⟩ hC _))
    (referenceSimpleRepresentative ⟨C, hC.toPiSuperfusionLaws⟩ hC
      (Multiplicative.toAdd (t.data.rho g))).laws.simple⟩

noncomputable def pullbackDegreeSimple (g : t.data.group) :
    SimpleObject (twistedPullback C hC t).toWeaklyPointedSuperfusion :=
  ⟨pullbackDegreeSimpleData C hC t g, pullbackDegreeSimpleLaws C hC t g⟩

end RMod.Classification
