import RMod.Classification.Instances.GaugeUnitOutput
import RMod.Classification.Proofs.ConvolutionUnitIndex
import RMod.Classification.Proofs.IsoCalculus

/-!
# The mapped source unitors on the gauge output inclusions

Interchange with the even identity parity map reduces these equations
to the exact source convolution unit-block formulas. These are equations
for the existing inclusions, not choices of new direct-sum presentations.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (d : GaugeData s.data t.data)

theorem gaugeLeftUnitOutput_evenIso (X : PullbackObj C s.data) (k : t.data.group) :
    EvenIsoLaws C.toWeaklyPointedSuperfusionData (gaugeLeftUnitOutputData C hC s t d X k) :=
  ((EvenIsoLaws.ofEq hC.toWeaklyPointedSuperfusionLaws _).trans hC.toWeaklyPointedSuperfusionLaws
    (evenIsoLaws_ofEvenIso ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
      (convolutionLeftUnitBlock C hC s.data s.laws X (d.phi.symm k)))).tensor
        hC.toWeaklyPointedSuperfusionLaws (EvenIsoLaws.refl hC.toWeaklyPointedSuperfusionLaws _)

theorem gaugeRightUnitOutput_evenIso (X : PullbackObj C s.data) (k : t.data.group) :
    EvenIsoLaws C.toWeaklyPointedSuperfusionData (gaugeRightUnitOutputData C hC s t d X k) :=
  (evenIsoLaws_ofEvenIso ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
    (convolutionRightUnitBlock C hC s.data s.laws X (d.phi.symm k))).tensor
      hC.toWeaklyPointedSuperfusionLaws (EvenIsoLaws.refl hC.toWeaklyPointedSuperfusionLaws _)

theorem gaugeLeftUnitOutput_inclusion (X : PullbackObj C s.data) (k : t.data.group) :
    C.comp (C.tensorHom
      (convolutionInclusion C hC s.data (pullbackUnitObj C hC s.data) X (d.phi.symm k) (d.phi.symm 1))
      (C.id (C.pi.factor (d.lam (d.phi.symm k)))))
      (C.tensorHom (convolutionLeftUnitorData C hC s.data s.laws X (d.phi.symm k)).hom
        (C.id (C.pi.factor (d.lam (d.phi.symm k))))) =
      (gaugeLeftUnitOutputData C hC s t d X k).hom := by
  rw [interchange_second_even hC.toWeaklyPointedSuperfusionLaws _ _ _ _ (hC.id_even _),
    hC.id_comp, convolutionLeftUnitor_inclusion_of_eq C hC s.data s.laws X _ _ (map_one d.phi.symm)]
  rfl

theorem gaugeRightUnitOutput_inclusion (X : PullbackObj C s.data) (k : t.data.group) :
    C.comp (C.tensorHom
      (convolutionInclusion C hC s.data X (pullbackUnitObj C hC s.data) (d.phi.symm k) (d.phi.symm k))
      (C.id (C.pi.factor (d.lam (d.phi.symm k)))))
      (C.tensorHom (convolutionRightUnitorData C hC s.data s.laws X (d.phi.symm k)).hom
        (C.id (C.pi.factor (d.lam (d.phi.symm k))))) =
      (gaugeRightUnitOutputData C hC s t d X k).hom := by
  rw [interchange_second_even hC.toWeaklyPointedSuperfusionLaws _ _ _ _ (hC.id_even _),
    hC.id_comp, convolutionRightUnitor_inclusion]
  rfl

end RMod.Classification
