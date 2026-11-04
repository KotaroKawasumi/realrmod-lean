import RMod.Classification.Proofs.ReconstructionProductTripleTensorators
import RMod.Classification.Proofs.ReconstructionTripleTensoratorCoherence
import RMod.Classification.Proofs.ConvolutionProductAssociator
import RMod.Classification.Proofs.IsoEqualityCancellation
import RMod.Classification.Instances.ReconstructionCoherenceData

/-!
# Reconstruction's monoidal associativity on every triple summand

Both global tensorator routes restrict to the retained component routes.
The extracted scalar equation compares those routes through the mapped
source associator. The actual convolution associator has the same local
block. Naturality of the final product-index equality compares the two
right routes, and cancelling that equality gives the required equation
in the original fixed output component.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)
  (X Y Z : LinearCategory A.toWeaklyPointedSuperfusion)
  (g h k : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionProductInsertion_associativity :
    let F := (reconstructionUnderlyingEquivalence A C hC).functor
    let t := reconstructionTwistData A C hC
    C.data.comp (convolutionProductLeftInsertion C.data hC t (F.obj X) (F.obj Y) (F.obj Z) g h k)
      (C.data.comp (C.data.comp
        (convolutionHom C.data hC t (fun q => (reconstructionTensoratorData A C hC X Y q).hom)
          (fun q => C.data.id (F.obj Z q).val) ((g * h) * k))
        (reconstructionTensoratorData A C hC (A.data.tensorObj X Y) Z ((g * h) * k)).hom)
        (F.map (A.data.associatorHom X Y Z) ((g * h) * k))) =
    C.data.comp (convolutionProductLeftInsertion C.data hC t (F.obj X) (F.obj Y) (F.obj Z) g h k)
      (C.data.comp (reconstructionAssociatorData A C hC (F.obj X) (F.obj Y) (F.obj Z) ((g * h) * k)).hom
        (C.data.comp (convolutionHom C.data hC t (fun q => C.data.id (F.obj X q).val)
          (fun q => (reconstructionTensoratorData A C hC Y Z q).hom) ((g * h) * k))
          (reconstructionTensoratorData A C hC X (A.data.tensorObj Y Z) ((g * h) * k)).hom)) := by
  dsimp only
  let F := (reconstructionUnderlyingEquivalence A C hC).functor
  let t := reconstructionTwistData A C hC
  let L : C.data.Obj := C.data.tensorObj
    (C.data.tensorObj (twistSummand C.data t (F.obj X) (F.obj Y) g h) (F.obj Z k).val)
    (C.data.pi.factor (reconstructionNu A C hC (g * h) k))
  let R : C.data.Obj := C.data.tensorObj
    (C.data.tensorObj (F.obj X g).val (twistSummand C.data t (F.obj Y) (F.obj Z) h k))
    (C.data.pi.factor (reconstructionNu A C hC g (h * k)))
  let D : SimpleOrbit A.toWeaklyPointedSuperfusion → C.data.Obj := fun q =>
    (convolutionObj C.data hC t (convolutionObj C.data hC t (F.obj X) (F.obj Y)) (F.obj Z) q).val
  let E : SimpleOrbit A.toWeaklyPointedSuperfusion → C.data.Obj := fun q =>
    (convolutionObj C.data hC t (F.obj X) (convolutionObj C.data hC t (F.obj Y) (F.obj Z)) q).val
  let U : SimpleOrbit A.toWeaklyPointedSuperfusion → C.data.Obj := fun q =>
    (F.obj (A.data.tensorObj (A.data.tensorObj X Y) Z) q).val
  let V : SimpleOrbit A.toWeaklyPointedSuperfusion → C.data.Obj := fun q =>
    (F.obj (A.data.tensorObj X (A.data.tensorObj Y Z)) q).val
  let i : C.data.Hom L (D ((g * h) * k)) := convolutionProductLeftInsertion C.data hC t (F.obj X) (F.obj Y) (F.obj Z) g h k
  let j : C.data.Hom R (E (g * (h * k))) := convolutionProductRightInsertion C.data hC t (F.obj X) (F.obj Y) (F.obj Z) g h k
  let ml : ∀ q, C.data.Hom (D q) (U q) := fun q => C.data.comp
    (convolutionHom C.data hC t (fun r => (reconstructionTensoratorData A C hC X Y r).hom)
      (fun r => C.data.id (F.obj Z r).val) q)
    (reconstructionTensoratorData A C hC (A.data.tensorObj X Y) Z q).hom
  let mr : ∀ q, C.data.Hom (E q) (V q) := fun q => C.data.comp
    (convolutionHom C.data hC t (fun r => C.data.id (F.obj X r).val)
      (fun r => (reconstructionTensoratorData A C hC Y Z r).hom) q)
    (reconstructionTensoratorData A C hC X (A.data.tensorObj Y Z) q).hom
  let n : C.data.Hom (U ((g * h) * k)) (V ((g * h) * k)) := F.map (A.data.associatorHom X Y Z) ((g * h) * k)
  let a : C.data.Hom (D ((g * h) * k)) (E ((g * h) * k)) :=
    (reconstructionAssociatorData A C hC (F.obj X) (F.obj Y) (F.obj Z) ((g * h) * k)).hom
  let eD : E ((g * h) * k) = E (g * (h * k)) := congrArg E (mul_assoc g h k)
  let eT : V ((g * h) * k) = V (g * (h * k)) := congrArg V (mul_assoc g h k)
  let p : Pi C.toWeaklyPointedSuperfusion.data := ⟨C.data.pi, C.laws.pi⟩
  let d := reconstructionComponentSystem A C hC
  let hS := simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion
  let hT := reconstruction_target_product A C hC
  let ν := reconstructionNu A C hC
  let θ := normalizedReconstructionComparison A C hC
  let x := (reconstructionSourceEquivalence A).inverse.obj X g
  let y := (reconstructionSourceEquivalence A).inverse.obj Y h
  let z := (reconstructionSourceEquivalence A).inverse.obj Z k
  let sL : C.data.Hom L (U ((g * h) * k)) := C.data.comp
    (componentTripleLeftTensorator p d hS hT ν θ g h k x y z).hom
    (reconstructionMappedTripleLeftInclusion A C hC X Y Z g h k)
  let sR : C.data.Hom R (V (g * (h * k))) := C.data.comp
    (componentTripleRightTensorator p d hS hT ν θ g h k x y z).hom
    (reconstructionMappedTripleRightInclusion A C hC X Y Z g h k)
  let c : C.data.Hom L R := (C.data.pi.localAssociator (F.obj X g).val (F.obj Y h).val (F.obj Z k).val
    (ν g h) (ν (g * h) k) (ν h k) (ν g (h * k))
    (reconstruction_normalizer_parity A C hC g h k) (reconstructionOmega A C hC g h k)).hom
  have hL : C.data.comp i (ml ((g * h) * k)) = sL :=
    (C.laws.comp_assoc _ _ _).symm.trans (reconstructionProductLeftInsertion_tensorators A C hC X Y Z g h k)
  have hR : C.data.comp j (mr (g * (h * k))) = sR :=
    (C.laws.comp_assoc _ _ _).symm.trans (reconstructionProductRightInsertion_tensorators A C hC X Y Z g h k)
  have hcomp : C.data.comp sL (C.data.comp n (IsoData.ofEq C.toWeaklyPointedSuperfusion.data eT).hom) = C.data.comp c sR :=
    reconstructionTripleTensorator_associativity A C hC X Y Z g h k
  have hmodel : C.data.comp (C.data.comp i a) (IsoData.ofEq C.toWeaklyPointedSuperfusion.data eD).hom = C.data.comp c j :=
    convolutionProductInsertion_associator C.data hC t (reconstruction_normalizer_parity A C hC)
      (F.obj X) (F.obj Y) (F.obj Z) g h k
  have hindex : C.data.comp (mr ((g * h) * k)) (IsoData.ofEq C.toWeaklyPointedSuperfusion.data eT).hom =
      C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data eD).hom (mr (g * (h * k))) :=
    indexed_morphism_eq_naturality C.toWeaklyPointedSuperfusion E V mr (mul_assoc g h k) eD eT
  change C.data.comp i (C.data.comp (ml ((g * h) * k)) n) = C.data.comp i (C.data.comp a (mr ((g * h) * k)))
  apply isoData_ofEq_cancel_right C.toWeaklyPointedSuperfusion eT
  have hl : C.data.comp (C.data.comp i (C.data.comp (ml ((g * h) * k)) n))
      (IsoData.ofEq C.toWeaklyPointedSuperfusion.data eT).hom = C.data.comp c sR := by
    calc
      _ = C.data.comp (C.data.comp (C.data.comp i (ml ((g * h) * k))) n)
          (IsoData.ofEq C.toWeaklyPointedSuperfusion.data eT).hom :=
        congrArg (fun m => C.data.comp m (IsoData.ofEq C.toWeaklyPointedSuperfusion.data eT).hom) (C.laws.comp_assoc _ _ _).symm
      _ = C.data.comp (C.data.comp sL n) (IsoData.ofEq C.toWeaklyPointedSuperfusion.data eT).hom :=
        congrArg (fun m => C.data.comp (C.data.comp m n) (IsoData.ofEq C.toWeaklyPointedSuperfusion.data eT).hom) hL
      _ = _ := (C.laws.comp_assoc _ _ _).trans hcomp
  have hr : C.data.comp (C.data.comp i (C.data.comp a (mr ((g * h) * k))))
      (IsoData.ofEq C.toWeaklyPointedSuperfusion.data eT).hom = C.data.comp c sR := by
    calc
      _ = C.data.comp (C.data.comp (C.data.comp i a) (mr ((g * h) * k)))
          (IsoData.ofEq C.toWeaklyPointedSuperfusion.data eT).hom :=
        congrArg (fun m => C.data.comp m (IsoData.ofEq C.toWeaklyPointedSuperfusion.data eT).hom) (C.laws.comp_assoc _ _ _).symm
      _ = C.data.comp (C.data.comp i a)
          (C.data.comp (mr ((g * h) * k)) (IsoData.ofEq C.toWeaklyPointedSuperfusion.data eT).hom) := C.laws.comp_assoc _ _ _
      _ = C.data.comp (C.data.comp i a)
          (C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data eD).hom (mr (g * (h * k)))) :=
        congrArg (C.data.comp (C.data.comp i a)) hindex
      _ = C.data.comp (C.data.comp (C.data.comp i a) (IsoData.ofEq C.toWeaklyPointedSuperfusion.data eD).hom)
          (mr (g * (h * k))) := (C.laws.comp_assoc _ _ _).symm
      _ = C.data.comp (C.data.comp c j) (mr (g * (h * k))) := congrArg (fun m => C.data.comp m (mr (g * (h * k)))) hmodel
      _ = C.data.comp c (C.data.comp j (mr (g * (h * k)))) := C.laws.comp_assoc _ _ _
      _ = _ := congrArg (C.data.comp c) hR
  exact hl.trans hr.symm

end RMod.Classification
