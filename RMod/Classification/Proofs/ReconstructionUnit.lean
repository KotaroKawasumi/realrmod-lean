import RMod.Classification.Instances.ReconstructionUnit
import RMod.Classification.Proofs.ReconstructionNeutralUnit
import RMod.Classification.Proofs.PullbackUnitLaws

/-!
# The global unit comparison is an even isomorphism

The supported coordinate uses the neutral component's proven inverse
maps. At every other coordinate both identities vanish, so the chosen
zero maps satisfy both inverse equations and are even.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

theorem reconstructionUnit_evenIso (k : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    EvenIsoLaws C.toWeaklyPointedSuperfusion.data (reconstructionUnitData A C hC k) := by
  classical
  by_cases hk : k = 1
  · subst k
    simp only [reconstructionUnitData]
    exact (EvenIsoLaws.ofEq C.laws.toWeaklyPointedSuperfusionLaws _).trans
      C.laws.toWeaklyPointedSuperfusionLaws (reconstructionNeutralUnit_even A C hC)
  · simp only [reconstructionUnitData, dif_neg hk]
    refine ⟨⟨?_, ?_⟩, C.laws.grade_zero _ _ _, C.laws.grade_zero _ _ _⟩
    · exact (raw_zero_comp C.laws.toWeaklyPointedSuperfusionLaws _).trans
        (pullbackUnit_supported C.data hC (reconstructionTwistData A C hC) k hk).symm
    · exact (raw_zero_comp C.laws.toWeaklyPointedSuperfusionLaws _).trans
        (reconstructionUnitImage_id_zero A C hC k hk).symm

/-- At the identity coordinate the actual comparison retains the supported-unit equality. -/
theorem reconstructionUnit_one_hom (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data) :
    (reconstructionUnitData A C hC 1).hom =
      C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
        (supportedObj_one C.data hC (reconstructionTwistData A C hC) _ _)).hom
        (reconstructionNeutralUnitData A C hC).hom := by
  simp only [reconstructionUnitData, dite_true, IsoData.trans]
  rfl

end RMod.Classification
