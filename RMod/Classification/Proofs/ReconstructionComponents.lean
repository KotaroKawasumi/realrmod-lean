import RMod.Classification.Proofs.SimpleOrbitRepresentatives
import RMod.Classification.Instances.ReferenceSimpleRepresentatives
import RMod.Classification.Proofs.ComponentComparison
import RMod.Classification.Proofs.UnitComponentComparison

/-!
# Component equivalences indexed by the intrinsic group

The normalized source representative has its intrinsic group type, and
the reference representative has that same type. The existing actual
component-equivalence construction therefore applies at every group
element. The type-zero convention fixes both unit representatives.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem exists_reconstructionComponent (A C : PiSuperfusion.{0, 0})
    (hC : ReferenceProperty C.data) (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    Nonempty (SpanSuperequivalence A.toWeaklyPointedSuperfusion C.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g).data.object
      (referenceSimpleRepresentative C hC (simpleOrbitType A g)).data.object) :=
  exists_componentComparison A C _ _
    (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g).laws.simple
    (referenceSimpleRepresentative C hC (simpleOrbitType A g)).laws.simple
    (simpleOrbitRepresentative_type A g) (referenceSimpleRepresentative_type C hC _)

theorem reconstruction_reference_one (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data) :
    referenceSimpleRepresentative C hC (simpleOrbitType A 1) = unitSimple C.toWeaklyPointedSuperfusion := by
  rw [simpleOrbitType_one, referenceSimpleRepresentative_zero]

/-- Choose the identity component through its split real unit algebra.
The condition at one retains an actual even unit isomorphism. -/
theorem exists_reconstructionComponent_with_unit (A C : PiSuperfusion.{0, 0})
    (hC : ReferenceProperty C.data) (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    ∃ E : SpanSuperequivalence A.toWeaklyPointedSuperfusion C.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g).data.object
      (referenceSimpleRepresentative C hC (simpleOrbitType A g)).data.object,
      g = 1 → ∃ i : IsoData C.data.toWeaklyPointedSuperfusionData C.data.tensorUnit
        (E.forwardFunctor.data.obj (spanGenerator A.toWeaklyPointedSuperfusion
          (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g).data.object)).obj,
        EvenIsoLaws C.data.toWeaklyPointedSuperfusionData i := by
  by_cases hg : g = 1
  · subst g
    rw [simpleOrbitRepresentative_one, reconstruction_reference_one]
    obtain ⟨E, i, hi⟩ := exists_unitComponentComparison A C
    exact ⟨E, fun _ => ⟨i, hi⟩⟩
  · obtain ⟨E⟩ := exists_reconstructionComponent A C hC g
    exact ⟨E, fun h => (hg h).elim⟩

end RMod.Classification
