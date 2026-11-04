import RMod.Classification.Instances.ComponentSystem
import RMod.Classification.Proofs.ReconstructionComponents

/-!
# Choosing the reconstruction's component system

Every chosen component is an actual superlinear equivalence. The choice
at the identity retains the even unit comparison proved by realization
of the split real unit algebra. Data contain these maps and inverses;
laws certify the same choices and the normalized generators.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

noncomputable def reconstructionComponentEquivalence
    (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    SpanSuperequivalence A.toWeaklyPointedSuperfusion C.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g).data.object
      (referenceSimpleRepresentative C hC (simpleOrbitType A g)).data.object :=
  (exists_reconstructionComponent_with_unit A C hC g).choose

noncomputable def reconstructionUnitComparisonData :
    IsoData C.data.toWeaklyPointedSuperfusionData C.data.tensorUnit
      ((reconstructionComponentEquivalence A C hC 1).forwardFunctor.data.obj
        (spanGenerator A.toWeaklyPointedSuperfusion
          (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion 1).data.object)).obj :=
  ((exists_reconstructionComponent_with_unit A C hC 1).choose_spec rfl).choose

theorem reconstructionUnitComparisonLaws :
    EvenIsoLaws C.data.toWeaklyPointedSuperfusionData (reconstructionUnitComparisonData A C hC) :=
  ((exists_reconstructionComponent_with_unit A C hC 1).choose_spec rfl).choose_spec

noncomputable def reconstructionComponentSystemData :
    ComponentSystemData A.toWeaklyPointedSuperfusion C.toWeaklyPointedSuperfusion
      (SimpleOrbit A.toWeaklyPointedSuperfusion)
      (fun g => (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g).data.object)
      (fun g => (referenceSimpleRepresentative C hC (simpleOrbitType A g)).data.object) where
  component g := (reconstructionComponentEquivalence A C hC g).data
  unitIso := reconstructionUnitComparisonData A C hC

theorem reconstructionComponentSystemLaws :
    ComponentSystemLaws A.toWeaklyPointedSuperfusion C.toWeaklyPointedSuperfusion
      (SimpleOrbit A.toWeaklyPointedSuperfusion) _ _ (reconstructionComponentSystemData A C hC) where
  component g := (reconstructionComponentEquivalence A C hC g).laws
  source_unit := congrArg (fun S => S.data.object)
    (simpleOrbitRepresentative_one A.toWeaklyPointedSuperfusion)
  target_unit := congrArg (fun S => S.data.object) (reconstruction_reference_one A C hC)
  unit_even := reconstructionUnitComparisonLaws A C hC

noncomputable def reconstructionComponentSystem :
    ComponentSystem A.toWeaklyPointedSuperfusion C.toWeaklyPointedSuperfusion
      (SimpleOrbit A.toWeaklyPointedSuperfusion)
      (fun g => (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g).data.object)
      (fun g => (referenceSimpleRepresentative C hC (simpleOrbitType A g)).data.object) :=
  ⟨reconstructionComponentSystemData A C hC, reconstructionComponentSystemLaws A C hC⟩

end RMod.Classification
