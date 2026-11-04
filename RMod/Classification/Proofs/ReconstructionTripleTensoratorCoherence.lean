import RMod.Classification.Proofs.ReconstructionMappedTripleCoherence
import RMod.Classification.Proofs.ReconstructionTripleTensoratorFormula
import RMod.Classification.Proofs.ComponentOmegaAssociativity

/-!
# Reconstruction associativity on the actual triple source presentation

Combine the defining equation for the extracted scalar with the mapped
ambient associator equation. Both sides land in the same selected
component of the actual image of `X tensor (Y tensor Z)`. This is the
component equation to be assembled by the convolution inclusions.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)
  (X Y Z : LinearCategory A.toWeaklyPointedSuperfusion)
  (g h k : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionTripleTensorator_associativity :
    let p : Pi C.toWeaklyPointedSuperfusion.data := ⟨C.data.pi, C.laws.pi⟩
    let d := reconstructionComponentSystem A C hC
    let hS := simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion
    let hT := reconstruction_target_product A C hC
    let ν := reconstructionNu A C hC
    let t := normalizedReconstructionComparison A C hC
    let x := (reconstructionSourceEquivalence A).inverse.obj X g
    let y := (reconstructionSourceEquivalence A).inverse.obj Y h
    let z := (reconstructionSourceEquivalence A).inverse.obj Z k
    let F := (reconstructionUnderlyingEquivalence A C hC).functor
    C.data.comp
      (C.data.comp (componentTripleLeftTensorator p d hS hT ν t g h k x y z).hom
        (reconstructionMappedTripleLeftInclusion A C hC X Y Z g h k))
      (C.data.comp (F.map (A.data.associatorHom X Y Z) ((g * h) * k))
        (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
          (congrArg (fun j => (F.obj (A.data.tensorObj X (A.data.tensorObj Y Z)) j).val)
            (mul_assoc g h k))).hom) =
    C.data.comp
      (C.data.pi.localAssociator (F.obj X g).val (F.obj Y h).val (F.obj Z k).val
        (ν g h) (ν (g * h) k) (ν h k) (ν g (h * k))
        (componentTripleParity d hS hT ν t g h k) (reconstructionOmega A C hC g h k)).hom
      (C.data.comp (componentTripleRightTensorator p d hS hT ν t g h k x y z).hom
        (reconstructionMappedTripleRightInclusion A C hC X Y Z g h k)) := by
  dsimp only
  let p : Pi C.toWeaklyPointedSuperfusion.data := ⟨C.data.pi, C.laws.pi⟩
  let d := reconstructionComponentSystem A C hC
  let hS := simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion
  let hT := reconstruction_target_product A C hC
  let ν := reconstructionNu A C hC
  let t := normalizedReconstructionComparison A C hC
  let x := (reconstructionSourceEquivalence A).inverse.obj X g
  let y := (reconstructionSourceEquivalence A).inverse.obj Y h
  let z := (reconstructionSourceEquivalence A).inverse.obj Z k
  let F := (reconstructionUnderlyingEquivalence A C hC).functor
  let L : C.data.Obj := C.data.tensorObj
    (C.data.tensorObj (C.data.tensorObj (C.data.tensorObj (F.obj X g).val (F.obj Y h).val)
      (C.data.pi.factor (ν g h))) (F.obj Z k).val) (C.data.pi.factor (ν (g * h) k))
  let R : C.data.Obj := C.data.tensorObj
    (C.data.tensorObj (F.obj X g).val
      (C.data.tensorObj (C.data.tensorObj (F.obj Y h).val (F.obj Z k).val)
        (C.data.pi.factor (ν h k)))) (C.data.pi.factor (ν g (h * k)))
  let Q : C.data.Obj := (reconstructionComponentRealization A C hC ((g * h) * k)).obj
    (reconstructionTripleLeftSpan A X Y Z g h k)
  let Q' : C.data.Obj := (reconstructionComponentRealization A C hC (g * (h * k))).obj
    (reconstructionTripleRightSpan A X Y Z g h k)
  let T : C.data.Obj := (F.obj (A.data.tensorObj (A.data.tensorObj X Y) Z) ((g * h) * k)).val
  let V : C.data.Obj := (F.obj (A.data.tensorObj X (A.data.tensorObj Y Z)) ((g * h) * k)).val
  let V' : C.data.Obj := (F.obj (A.data.tensorObj X (A.data.tensorObj Y Z)) (g * (h * k))).val
  let l : C.data.Hom L Q := (componentTripleLeftTensorator p d hS hT ν t g h k x y z).hom
  let r : C.data.Hom R Q' := (componentTripleRightTensorator p d hS hT ν t g h k x y z).hom
  let a : C.data.Hom Q Q' := (componentMappedTripleAssociator d hS hT g h k x y z).hom
  let b : C.data.Hom L R := (C.data.pi.localAssociator (F.obj X g).val (F.obj Y h).val
    (F.obj Z k).val (ν g h) (ν (g * h) k) (ν h k) (ν g (h * k))
    (componentTripleParity d hS hT ν t g h k) (reconstructionOmega A C hC g h k)).hom
  let i : C.data.Hom Q T := reconstructionMappedTripleLeftInclusion A C hC X Y Z g h k
  let j : C.data.Hom Q' V' := reconstructionMappedTripleRightInclusion A C hC X Y Z g h k
  let n : C.data.Hom T V := F.map (A.data.associatorHom X Y Z) ((g * h) * k)
  let e : C.data.Hom V V' := (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
    (congrArg (fun q => (F.obj (A.data.tensorObj X (A.data.tensorObj Y Z)) q).val)
      (mul_assoc g h k))).hom
  have hc : C.data.comp l a = C.data.comp b r :=
    componentOmega_associativity p d hS hT ν t g h k x y z
  have hm : C.data.comp (C.data.comp i n) e = C.data.comp a j :=
    reconstructionMappedTripleInclusion_associator A C hC X Y Z g h k
  change C.data.comp (C.data.comp l i) (C.data.comp n e) = C.data.comp b (C.data.comp r j)
  calc
    _ = C.data.comp l (C.data.comp i (C.data.comp n e)) := C.laws.comp_assoc _ _ _
    _ = C.data.comp l (C.data.comp (C.data.comp i n) e) :=
      congrArg (C.data.comp l) (C.laws.comp_assoc i n e).symm
    _ = C.data.comp l (C.data.comp a j) := congrArg (C.data.comp l) hm
    _ = C.data.comp (C.data.comp l a) j := (C.laws.comp_assoc _ _ _).symm
    _ = C.data.comp (C.data.comp b r) j := congrArg (fun m => C.data.comp m j) hc
    _ = _ := C.laws.comp_assoc _ _ _

end RMod.Classification
