import RMod.Classification.Instances.GaugeTensorBlock
import RMod.Classification.Instances.ConvolutionUnitors

/-!
# The source unitor after a gauge tensor block

On the surviving left unit block, inverse reindexing sends the first
index to phi inverse(1). Retain the equality with 1 before applying the
actual source unit block. On the right, the first index is already the
source output degree. Both comparisons are tensored with its parity line.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (d : GaugeData s.data t.data)

noncomputable def gaugeLeftUnitOutputData (X : PullbackObj C s.data) (k : t.data.group) :
    IsoData C.toWeaklyPointedSuperfusionData
      (C.tensorObj (twistSummand C s.data (pullbackUnitObj C hC s.data) X
        (d.phi.symm 1) ((d.phi.symm 1)⁻¹ * d.phi.symm k)) (C.pi.factor (d.lam (d.phi.symm k))))
      (C.tensorObj (X (d.phi.symm k)).val (C.pi.factor (d.lam (d.phi.symm k)))) :=
  ((IsoData.ofEq C.toWeaklyPointedSuperfusionData
    (congrArg (fun g => twistSummand C s.data (pullbackUnitObj C hC s.data) X
      g (g⁻¹ * d.phi.symm k)) (map_one d.phi.symm))).trans C.toWeaklyPointedSuperfusionData
    (IsoData.ofEvenIso ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
      (convolutionLeftUnitBlock C hC s.data s.laws X (d.phi.symm k)))).tensor
        C.toWeaklyPointedSuperfusionData (IsoData.refl C.toWeaklyPointedSuperfusionData
          (C.pi.factor (d.lam (d.phi.symm k))))

noncomputable def gaugeRightUnitOutputData (X : PullbackObj C s.data) (k : t.data.group) :
    IsoData C.toWeaklyPointedSuperfusionData
      (C.tensorObj (twistSummand C s.data X (pullbackUnitObj C hC s.data)
        (d.phi.symm k) ((d.phi.symm k)⁻¹ * d.phi.symm k)) (C.pi.factor (d.lam (d.phi.symm k))))
      (C.tensorObj (X (d.phi.symm k)).val (C.pi.factor (d.lam (d.phi.symm k)))) :=
  (IsoData.ofEvenIso ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
    (convolutionRightUnitBlock C hC s.data s.laws X (d.phi.symm k))).tensor
      C.toWeaklyPointedSuperfusionData (IsoData.refl C.toWeaklyPointedSuperfusionData
        (C.pi.factor (d.lam (d.phi.symm k))))

end RMod.Classification
