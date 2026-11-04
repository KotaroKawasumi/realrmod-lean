import RMod.Classification.Instances.GaugeProductTriple
import RMod.Classification.Proofs.GaugeSourceParity

/-!
# Source associator and output equality maps in target coordinates

The source normalizer keeps the inverse images of the intermediate
products. The final output transport changes both the convolution
degree and its right parity factor. Its local counterpart changes only
that final factor on the fixed right triple word.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (d : GaugeData s.data t.data)

noncomputable def gaugeProductSourceAssociatorData (X Y Z : PullbackObj C s.data) (g h k : t.data.group) :
    IsoData C.toWeaklyPointedSuperfusionData
      (C.tensorObj (C.tensorObj (twistSummand C s.data X Y (d.phi.symm g) (d.phi.symm h))
        (Z (d.phi.symm k)).val) (C.pi.factor (s.data.nu (d.phi.symm (g * h)) (d.phi.symm k))))
      (C.tensorObj (C.tensorObj (X (d.phi.symm g)).val
        (twistSummand C s.data Y Z (d.phi.symm h) (d.phi.symm k)))
        (C.pi.factor (s.data.nu (d.phi.symm g) (d.phi.symm (h * k))))) :=
  C.pi.localAssociator (X (d.phi.symm g)).val (Y (d.phi.symm h)).val (Z (d.phi.symm k)).val
    (s.data.nu (d.phi.symm g) (d.phi.symm h)) (s.data.nu (d.phi.symm (g * h)) (d.phi.symm k))
    (s.data.nu (d.phi.symm h) (d.phi.symm k)) (s.data.nu (d.phi.symm g) (d.phi.symm (h * k)))
    (gaugeSourceNormalizerParity s t d g h k) (s.data.omega (d.phi.symm g) (d.phi.symm h) (d.phi.symm k))

noncomputable def gaugeProductRightParityTransportData (X Y Z : PullbackObj C s.data) (g h k : t.data.group) :
    IsoData C.toWeaklyPointedSuperfusionData
      (C.tensorObj (C.tensorObj (C.tensorObj (X (d.phi.symm g)).val
        (twistSummand C s.data Y Z (d.phi.symm h) (d.phi.symm k)))
        (C.pi.factor (s.data.nu (d.phi.symm g) (d.phi.symm (h * k)))))
        (C.pi.factor (d.lam (d.phi.symm ((g * h) * k)))))
      (C.tensorObj (C.tensorObj (C.tensorObj (X (d.phi.symm g)).val
        (twistSummand C s.data Y Z (d.phi.symm h) (d.phi.symm k)))
        (C.pi.factor (s.data.nu (d.phi.symm g) (d.phi.symm (h * k)))))
        (C.pi.factor (d.lam (d.phi.symm (g * (h * k)))))) :=
  IsoData.ofEq C.toWeaklyPointedSuperfusionData (congrArg (fun j =>
    C.tensorObj (C.tensorObj (C.tensorObj (X (d.phi.symm g)).val
      (twistSummand C s.data Y Z (d.phi.symm h) (d.phi.symm k)))
      (C.pi.factor (s.data.nu (d.phi.symm g) (d.phi.symm (h * k)))))
      (C.pi.factor (d.lam (d.phi.symm j)))) (mul_assoc g h k))

noncomputable def gaugeProductOutputTransportData (X Y Z : PullbackObj C s.data) (g h k : t.data.group) :
    IsoData C.toWeaklyPointedSuperfusionData
      (C.tensorObj (convolutionObj C hC s.data X (convolutionObj C hC s.data Y Z)
        (d.phi.symm ((g * h) * k))).val (C.pi.factor (d.lam (d.phi.symm ((g * h) * k)))))
      (C.tensorObj (convolutionObj C hC s.data X (convolutionObj C hC s.data Y Z)
        (d.phi.symm (g * (h * k)))).val (C.pi.factor (d.lam (d.phi.symm (g * (h * k)))))) :=
  IsoData.ofEq C.toWeaklyPointedSuperfusionData (congrArg (fun j =>
    C.tensorObj (convolutionObj C hC s.data X (convolutionObj C hC s.data Y Z) (d.phi.symm j)).val
      (C.pi.factor (d.lam (d.phi.symm j)))) (mul_assoc g h k))

end RMod.Classification
