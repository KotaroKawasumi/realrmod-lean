import RMod.Classification.Proofs.ComponentSelectedUnitCoherence
import RMod.Classification.Proofs.ReconstructionSelectedUnitIndex
import RMod.Classification.Proofs.ReconstructionUnitSourceUnitor

/-!
# The reconstruction unit diagram on its actual selected components

Specialize component unit coherence to the retained isomorphism from the
unit generator to the selected source unit component. The target unit
map is exactly the previously constructed neutral comparison.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)
  (X : LinearCategory A.toWeaklyPointedSuperfusion)
  (g : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionLeftSelectedUnit_coherence :
    C.data.comp (C.data.comp
      (C.data.tensorHom (C.data.tensorHom (reconstructionNeutralUnitData A C hC).hom (C.data.id (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val)) (C.data.id C.data.tensorUnit))
      ((parityTensorComparison (⟨C.data.pi, C.laws.pi⟩ : Pi C.toWeaklyPointedSuperfusion.data)
        ((reconstructionComponentSystem A C hC).leftUnitComparison g
          (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion 1 g)
          (reconstruction_target_product A C hC 1 g))).data.app ((reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit 1) ((reconstructionSourceEquivalence A).inverse.obj X g)).hom)
      (C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
          (reconstructionLeftUnitComponent_obj A C hC X g)).hom
        ((reconstructionComponentRealization A C hC g).map (reconstructionLeftUnitSpanMap A X g))) =
      C.data.comp (C.data.rightUnitorHom (C.data.tensorObj C.data.tensorUnit (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val)) (C.data.leftUnitorHom (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val) := by
  exact componentLeftSelectedUnit_coherence
    (⟨C.data.pi, C.laws.pi⟩ : Pi C.toWeaklyPointedSuperfusion.data)
    (reconstructionComponentSystem A C hC) g
    (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion 1 g)
    (reconstruction_target_product A C hC 1 g) ((reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit 1) ((reconstructionSourceEquivalence A).inverse.obj X g)
    (reconstructionLeftUnitSpan A X g).property
    (reconstructionUnitSourceIsoData A) (reconstructionUnitSourceIso_even A)
    (reconstructionLeftUnitSpanMap A X g).hom
    (reconstructionUnitSource_left_unitor_inv A ((reconstructionSourceEquivalence A).inverse.obj X g).obj)

theorem reconstructionRightSelectedUnit_coherence :
    C.data.comp (C.data.comp
      (C.data.tensorHom (C.data.tensorHom (C.data.id (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val) (reconstructionNeutralUnitData A C hC).hom) (C.data.id C.data.tensorUnit))
      ((parityTensorComparison (⟨C.data.pi, C.laws.pi⟩ : Pi C.toWeaklyPointedSuperfusion.data)
        ((reconstructionComponentSystem A C hC).rightUnitComparison g
          (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion g 1)
          (reconstruction_target_product A C hC g 1))).data.app ((reconstructionSourceEquivalence A).inverse.obj X g) ((reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit 1)).hom)
      (C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
          (reconstructionRightUnitComponent_obj A C hC X g)).hom
        ((reconstructionComponentRealization A C hC g).map (reconstructionRightUnitSpanMap A X g))) =
      C.data.comp (C.data.rightUnitorHom (C.data.tensorObj (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val C.data.tensorUnit)) (C.data.rightUnitorHom (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val) := by
  exact componentRightSelectedUnit_coherence
    (⟨C.data.pi, C.laws.pi⟩ : Pi C.toWeaklyPointedSuperfusion.data)
    (reconstructionComponentSystem A C hC) g
    (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion g 1)
    (reconstruction_target_product A C hC g 1) ((reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit 1) ((reconstructionSourceEquivalence A).inverse.obj X g)
    (reconstructionRightUnitSpan A X g).property
    (reconstructionUnitSourceIsoData A) (reconstructionUnitSourceIso_even A)
    (reconstructionRightUnitSpanMap A X g).hom
    (reconstructionUnitSource_right_unitor_inv A ((reconstructionSourceEquivalence A).inverse.obj X g).obj)

end RMod.Classification
