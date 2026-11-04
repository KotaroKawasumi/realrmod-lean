import RMod.Classification.Proofs.ReconstructionUnitParityCoherence
import RMod.Classification.Proofs.ReconstructionUnit
import RMod.Classification.Proofs.UnitDiagramTransport

/-!
# The reconstruction unit equation on an actual binary summand

The supported unit object and extracted parity factor are transported
by their specified equality maps. Consequently the actual global unit
comparison and binary tensorator give the normalized ambient unitors.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)
  (X : LinearCategory A.toWeaklyPointedSuperfusion)
  (g : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionLeftUnitSummand_coherence
    (hs : C.data.tensorObj (C.data.tensorObj (pullbackUnitObj C.data hC (reconstructionTwistData A C hC) 1).val (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val) (C.data.pi.factor (reconstructionNu A C hC 1 g)) =
      C.data.tensorObj (C.data.tensorObj C.data.tensorUnit (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val) C.data.tensorUnit) :
    C.data.comp (C.data.comp
      (C.data.tensorHom (C.data.tensorHom (reconstructionUnitData A C hC 1).hom (C.data.id (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val)) (C.data.id (C.data.pi.factor (reconstructionNu A C hC 1 g))))
      ((reconstructionTensorComparison A C hC 1 g).data.app ((reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit 1) ((reconstructionSourceEquivalence A).inverse.obj X g)).hom)
      (C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
          (reconstructionLeftUnitComponent_obj A C hC X g)).hom
        ((reconstructionComponentRealization A C hC g).map (reconstructionLeftUnitSpanMap A X g))) =
      C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data hs).hom
        (C.data.comp (C.data.rightUnitorHom (C.data.tensorObj C.data.tensorUnit (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val)) (C.data.leftUnitorHom (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val)) := by
  rw [reconstructionUnit_one_hom]
  exact leftUnitDiagram_transport
    (⟨C.data.pi, C.laws.pi⟩ : Pi C.toWeaklyPointedSuperfusion.data)
    (supportedObj_one C.data hC (reconstructionTwistData A C hC) _ _)
    (reconstructionNu_one_left A C hC g) (reconstructionNeutralUnitData A C hC).hom
    ((reconstructionTensorComparison A C hC 1 g).data.app ((reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit 1) ((reconstructionSourceEquivalence A).inverse.obj X g)).hom
    (C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
        (reconstructionLeftUnitComponent_obj A C hC X g)).hom
      ((reconstructionComponentRealization A C hC g).map (reconstructionLeftUnitSpanMap A X g)))
    (reconstructionLeftUnitParity_coherence A C hC X g) hs

theorem reconstructionRightUnitSummand_coherence
    (hs : C.data.tensorObj (C.data.tensorObj (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val (pullbackUnitObj C.data hC (reconstructionTwistData A C hC) 1).val) (C.data.pi.factor (reconstructionNu A C hC g 1)) =
      C.data.tensorObj (C.data.tensorObj (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val C.data.tensorUnit) C.data.tensorUnit) :
    C.data.comp (C.data.comp
      (C.data.tensorHom (C.data.tensorHom (C.data.id (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val) (reconstructionUnitData A C hC 1).hom) (C.data.id (C.data.pi.factor (reconstructionNu A C hC g 1))))
      ((reconstructionTensorComparison A C hC g 1).data.app ((reconstructionSourceEquivalence A).inverse.obj X g) ((reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit 1)).hom)
      (C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
          (reconstructionRightUnitComponent_obj A C hC X g)).hom
        ((reconstructionComponentRealization A C hC g).map (reconstructionRightUnitSpanMap A X g))) =
      C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data hs).hom
        (C.data.comp (C.data.rightUnitorHom (C.data.tensorObj (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val C.data.tensorUnit)) (C.data.rightUnitorHom (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val)) := by
  rw [reconstructionUnit_one_hom]
  exact rightUnitDiagram_transport
    (⟨C.data.pi, C.laws.pi⟩ : Pi C.toWeaklyPointedSuperfusion.data)
    (supportedObj_one C.data hC (reconstructionTwistData A C hC) _ _)
    (reconstructionNu_one_right A C hC g) (reconstructionNeutralUnitData A C hC).hom
    ((reconstructionTensorComparison A C hC g 1).data.app ((reconstructionSourceEquivalence A).inverse.obj X g) ((reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit 1)).hom
    (C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
        (reconstructionRightUnitComponent_obj A C hC X g)).hom
      ((reconstructionComponentRealization A C hC g).map (reconstructionRightUnitSpanMap A X g)))
    (reconstructionRightUnitParity_coherence A C hC X g) hs

end RMod.Classification
