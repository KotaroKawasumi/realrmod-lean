import RMod.Classification.Proofs.ReconstructionTensorSpanInclusion

/-!
# Nested tensor-component inclusions equal the threefold presentation

The intermediate selected component projector cancels on the incoming
tensor span. Evenness removes the super-interchange sign. Thus composing
the two retained binary inclusions gives the actual triple inclusion.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A : PiSuperfusion.{0, 0}) (X Y Z : LinearCategory A.toWeaklyPointedSuperfusion)
  (g h k : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionTripleLeftInclusion_nested :
    A.data.comp
      (A.data.tensorHom (reconstructionTensorSpanInclusion A X Y g h).hom
        (A.data.id ((reconstructionSourceEquivalence A).inverse.obj Z k).obj))
      (reconstructionTensorSpanInclusion A (A.data.tensorObj X Y) Z (g * h) k).hom =
      (reconstructionTripleLeftInclusion A X Y Z g h k).hom := by
  let i := (reconstructionTensorSpanInclusion A X Y g h).hom
  let j := (reconstructionSourceBicone A (A.data.tensorObj X Y)).ι (g * h)
  let z := (reconstructionSourceBicone A Z).ι k
  let iz := A.data.id ((reconstructionSourceEquivalence A).inverse.obj Z k).obj
  let xy := (reconstructionTensorBicone A X Y).ι (g, h)
  let q := (reconstructionSourceBicone A (A.data.tensorObj (A.data.tensorObj X Y) Z)).π ((g * h) * k)
  have hi : A.data.comp i j = xy := reconstructionTensorSpanInclusion_inclusion A X Y g h
  have ht : A.data.comp (A.data.tensorHom i iz) (A.data.tensorHom j z) = A.data.tensorHom xy z :=
    (interchange_second_even A.laws.toWeaklyPointedSuperfusionLaws j z i iz
      (reconstructionSourceBicone_inclusion_even A Z k)).trans
      (congrArg₂ A.data.tensorHom hi (A.laws.id_comp z))
  change A.data.comp (A.data.tensorHom i iz) (A.data.comp (A.data.tensorHom j z) q) =
    A.data.comp (A.data.tensorHom xy z) q
  exact (A.laws.comp_assoc _ _ _).symm.trans (congrArg (fun f => A.data.comp f q) ht)

theorem reconstructionTripleRightInclusion_nested :
    A.data.comp
      (A.data.tensorHom (A.data.id ((reconstructionSourceEquivalence A).inverse.obj X g).obj)
        (reconstructionTensorSpanInclusion A Y Z h k).hom)
      (reconstructionTensorSpanInclusion A X (A.data.tensorObj Y Z) g (h * k)).hom =
      (reconstructionTripleRightInclusion A X Y Z g h k).hom := by
  let i := (reconstructionTensorSpanInclusion A Y Z h k).hom
  let j := (reconstructionSourceBicone A (A.data.tensorObj Y Z)).ι (h * k)
  let x := (reconstructionSourceBicone A X).ι g
  let ix := A.data.id ((reconstructionSourceEquivalence A).inverse.obj X g).obj
  let yz := (reconstructionTensorBicone A Y Z).ι (h, k)
  let q := (reconstructionSourceBicone A (A.data.tensorObj X (A.data.tensorObj Y Z))).π (g * (h * k))
  have hi : A.data.comp i j = yz := reconstructionTensorSpanInclusion_inclusion A Y Z h k
  have ht : A.data.comp (A.data.tensorHom ix i) (A.data.tensorHom x j) = A.data.tensorHom x yz :=
    (interchange_first_even A.laws.toWeaklyPointedSuperfusionLaws x j ix i
      (A.laws.id_even _)).trans (congrArg₂ A.data.tensorHom (A.laws.id_comp x) hi)
  change A.data.comp (A.data.tensorHom ix i) (A.data.comp (A.data.tensorHom x j) q) =
    A.data.comp (A.data.tensorHom x yz) q
  exact (A.laws.comp_assoc _ _ _).symm.trans (congrArg (fun f => A.data.comp f q) ht)

end RMod.Classification
