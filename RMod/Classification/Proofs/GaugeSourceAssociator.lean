import RMod.Classification.Instances.GaugeProductAssociator
import RMod.Classification.Proofs.GaugeIndexedSourceInsertions
import RMod.Classification.Proofs.TensorIndexedOutputEquality

/-!
# The source associator on the transported gauge triple insertions

The indexed convolution theorem identifies the unshifted local block.
Tensoring that equation together with its output-index comparison moves
the final parity factor to the right output degree. Thus the actual
source associator has the required local formula with all transports.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (d : GaugeData s.data t.data)

theorem gaugeProductSourceInsertion_associator (X Y Z : PullbackObj C s.data) (g h k : t.data.group) :
    C.comp (C.comp (gaugeProductLeftSourceInsertion C hC s t d X Y Z g h k)
      (C.tensorHom (convolutionAssociatorDataOfParity C hC s.data s.laws.normalizer_parity X Y Z
        (d.phi.symm ((g * h) * k))).hom (C.id (C.pi.factor (d.lam (d.phi.symm ((g * h) * k)))))))
      (gaugeProductOutputTransportData C hC s t d X Y Z g h k).hom =
      C.comp (C.comp (C.tensorHom (gaugeProductSourceAssociatorData C s t d X Y Z g h k).hom
        (C.id (C.pi.factor (d.lam (d.phi.symm ((g * h) * k))))))
        (gaugeProductRightParityTransportData C s t d X Y Z g h k).hom)
        (gaugeProductRightSourceInsertion C hC s t d X Y Z g h k) := by
  let l := convolutionIndexedLeftInsertion C hC s.data X Y Z
    (d.phi.symm g) (d.phi.symm h) (d.phi.symm k) (d.phi.symm (g * h)) (d.phi.symm ((g * h) * k))
    (map_mul d.phi.symm g h).symm (map_mul d.phi.symm (g * h) k).symm
  let r := convolutionIndexedRightInsertion C hC s.data X Y Z
    (d.phi.symm g) (d.phi.symm h) (d.phi.symm k) (d.phi.symm (h * k)) (d.phi.symm (g * (h * k)))
    (map_mul d.phi.symm h k).symm (map_mul d.phi.symm g (h * k)).symm
  let a := (gaugeProductSourceAssociatorData C s t d X Y Z g h k).hom
  let A := (convolutionAssociatorDataOfParity C hC s.data s.laws.normalizer_parity X Y Z
    (d.phi.symm ((g * h) * k))).hom
  let O := fun j => (convolutionObj C hC s.data X (convolutionObj C hC s.data Y Z) j).val
  let P := fun j => C.pi.factor (d.lam j)
  let e := congrArg d.phi.symm (mul_assoc g h k)
  have he : C.comp (C.comp l A) (IsoData.ofEq C.toWeaklyPointedSuperfusionData (congrArg O e)).hom =
      C.comp a r :=
    convolutionIndexedInsertion_associator C hC s.data s.laws.normalizer_parity X Y Z
      (d.phi.symm g) (d.phi.symm h) (d.phi.symm k) (d.phi.symm (g * h)) (d.phi.symm (h * k))
      (d.phi.symm ((g * h) * k)) (d.phi.symm (g * (h * k)))
      (map_mul d.phi.symm g h).symm (map_mul d.phi.symm h k).symm
      (map_mul d.phi.symm (g * h) k).symm (map_mul d.phi.symm g (h * k)).symm e
      (gaugeSourceNormalizerParity s t d g h k)
  have ht := tensor_indexed_output_comparison hC.toWeaklyPointedSuperfusionLaws O P e (C.comp l A) r a he
  rw [gaugeProductLeftSourceInsertion_eq_indexed, gaugeProductRightSourceInsertion_eq_indexed]
  let Pf := P (d.phi.symm ((g * h) * k))
  have hm : C.tensorHom (C.comp l A) (C.id Pf) =
      C.comp (C.tensorHom l (C.id Pf)) (C.tensorHom A (C.id Pf)) :=
    (tensorRightLaws ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
      Pf).map_comp l A
  rw [← hm]
  exact ht

end RMod.Classification
