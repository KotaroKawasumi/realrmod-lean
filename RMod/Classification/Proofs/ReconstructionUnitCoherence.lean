import RMod.Classification.Proofs.ReconstructionUnitBlockCoherence
import RMod.Classification.Proofs.ReconstructionMappedUnitOutput
import RMod.Classification.Proofs.ReconstructionTensoratorInsertions
import RMod.Classification.Proofs.ConvolutionUnitInsertionsOfParity
import RMod.Classification.Instances.ReconstructionCoherenceData

/-!
# The global reconstruction functor preserves both unitors

Convolution inclusions detect equality. Every summand away from the unit
support has zero identity. On the surviving summand, the actual global
tensorator, mapped source unitor, and unit comparison reduce to the
proved binary unit equation. No scalar coherence law is assumed.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)
  (X : LinearCategory A.toWeaklyPointedSuperfusion)
  (k : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionTensorator_left_unit :
    C.data.comp (C.data.comp
      (convolutionHom C.data hC (reconstructionTwistData A C hC) (fun g => (reconstructionUnitData A C hC g).hom) (fun g => C.data.id (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val) k)
      (reconstructionTensoratorData A C hC A.data.tensorUnit X k).hom)
      ((reconstructionUnderlyingEquivalence A C hC).functor.map (A.data.leftUnitorHom X) k) =
    (reconstructionLeftUnitorData A C hC
      ((reconstructionUnderlyingEquivalence A C hC).functor.obj X) k).hom := by
  classical
  let F := (reconstructionUnderlyingEquivalence A C hC).functor
  let t := reconstructionTwistData A C hC
  let U := pullbackUnitObj C.data hC t
  let u : PullbackHom C.data t U (F.obj A.data.tensorUnit) := fun g => (reconstructionUnitData A C hC g).hom
  let iX : PullbackHom C.data t (F.obj X) (F.obj X) := fun g => C.data.id (F.obj X g).val
  apply hom_ext_of_convolutionInclusions C.data hC t U (F.obj X) k
  intro a₀
  let a : SimpleOrbit A.toWeaklyPointedSuperfusion := a₀
  by_cases ha : a = 1
  · have ha₀ : a₀ = 1 := ha
    subst a₀
    let D : C.data.Obj := (convolutionObj C.data hC t U (F.obj X) k).val
    let D' : C.data.Obj := (convolutionObj C.data hC t (F.obj A.data.tensorUnit) (F.obj X) k).val
    let P : C.data.Obj := (F.obj (A.data.tensorObj A.data.tensorUnit X) k).val
    let Z : C.data.Obj := (F.obj X k).val
    let L : C.data.Obj := twistSummand C.data t U (F.obj X) 1 ((1 : SimpleOrbit A.toWeaklyPointedSuperfusion)⁻¹ * k)
    let L' : C.data.Obj := twistSummand C.data t (F.obj A.data.tensorUnit) (F.obj X) 1 ((1 : SimpleOrbit A.toWeaklyPointedSuperfusion)⁻¹ * k)
    let R : C.data.Obj := (reconstructionComponentRealization A C hC k).obj
      (reconstructionTensorOutputSpan A A.data.tensorUnit X k 1)
    let i : C.data.Hom L D := convolutionInclusion C.data hC t U (F.obj X) k 1
    let i' : C.data.Hom L' D' := convolutionInclusion C.data hC t (F.obj A.data.tensorUnit) (F.obj X) k 1
    let c : C.data.Hom D D' := convolutionHom C.data hC t u iX k
    let m : C.data.Hom D' P := (reconstructionTensoratorData A C hC A.data.tensorUnit X k).hom
    let n : C.data.Hom P Z := F.map (A.data.leftUnitorHom X) k
    let b : C.data.Hom L' R := (reconstructionConvolutionBlockIso A C hC A.data.tensorUnit X k 1).hom.hom
    let j : C.data.Hom R P := (reconstructionMappedTensorBicone A C hC A.data.tensorUnit X k).ι 1
    let v : C.data.Hom L L' := twistSummandHom C.data t u iX 1 ((1 : SimpleOrbit A.toWeaklyPointedSuperfusion)⁻¹ * k)
    let q : C.data.Hom R Z := C.data.comp
      (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
        (congrArg (reconstructionComponentRealization A C hC k).obj
          (reconstructionLeftUnitOutput_eq A X k))).hom
      ((reconstructionComponentRealization A C hC k).map (reconstructionLeftUnitSpanMap A X k))
    let w : C.data.Hom L Z := (convolutionLeftUnitBlockOfParity C.data hC t
      (reconstructionNu_one_left A C hC) (F.obj X) k).hom.hom
    let l : C.data.Hom D Z := (reconstructionLeftUnitorData A C hC (F.obj X) k).hom
    have hc : C.data.comp i c = C.data.comp v i' := convolutionInclusion_map C.data hC t u iX k 1
    have hm : C.data.comp i' m = C.data.comp b j := reconstructionTensorator_inclusion A C hC A.data.tensorUnit X k 1
    have hn : C.data.comp j n = q := by
      have hh := reconstructionMappedLeftUnitOutput_map A C hC X k
      rw [linear_eqToHom_eq_ofEq] at hh
      exact hh
    have hv : C.data.comp v (C.data.comp b q) = w := reconstructionLeftUnitBlock_coherence A C hC X k
    have hl : C.data.comp i l = w := convolutionLeftUnitor_inclusionOfParity C.data hC t
      (reconstructionNu_one_left A C hC) (F.obj X) k
    change C.data.comp i (C.data.comp (C.data.comp c m) n) = C.data.comp i l
    calc
      _ = C.data.comp (C.data.comp i c) (C.data.comp m n) :=
        (congrArg (C.data.comp i) (C.laws.comp_assoc c m n)).trans (C.laws.comp_assoc _ _ _).symm
      _ = C.data.comp (C.data.comp v i') (C.data.comp m n) := congrArg (fun z => C.data.comp z _) hc
      _ = C.data.comp v (C.data.comp (C.data.comp i' m) n) :=
        (C.laws.comp_assoc _ _ _).trans (congrArg (C.data.comp v) (C.laws.comp_assoc _ _ _).symm)
      _ = C.data.comp v (C.data.comp (C.data.comp b j) n) :=
        congrArg (fun z => C.data.comp v (C.data.comp z n)) hm
      _ = C.data.comp v (C.data.comp b (C.data.comp j n)) :=
        congrArg (C.data.comp v) (C.laws.comp_assoc _ _ _)
      _ = C.data.comp v (C.data.comp b q) := congrArg (fun z => C.data.comp v (C.data.comp b z)) hn
      _ = w := hv
      _ = _ := hl.symm
  · have hz : C.data.id (twistSummand C.data t U (F.obj X) a (a⁻¹ * k)) = C.data.zero := by
      exact tensor_id_zero_left C.laws.toWeaklyPointedSuperfusionLaws
        (tensor_id_zero_left C.laws.toWeaklyPointedSuperfusionLaws
          (pullbackUnit_id_zero C.data hC t a ha) (F.obj X (a⁻¹ * k)).val) _
    exact (hom_eq_zero_of_source C.laws.toWeaklyPointedSuperfusionLaws hz _).trans
      (hom_eq_zero_of_source C.laws.toWeaklyPointedSuperfusionLaws hz _).symm

theorem reconstructionTensorator_right_unit :
    C.data.comp (C.data.comp
      (convolutionHom C.data hC (reconstructionTwistData A C hC) (fun g => C.data.id (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val) (fun g => (reconstructionUnitData A C hC g).hom) k)
      (reconstructionTensoratorData A C hC X A.data.tensorUnit k).hom)
      ((reconstructionUnderlyingEquivalence A C hC).functor.map (A.data.rightUnitorHom X) k) =
    (reconstructionRightUnitorData A C hC
      ((reconstructionUnderlyingEquivalence A C hC).functor.obj X) k).hom := by
  classical
  let F := (reconstructionUnderlyingEquivalence A C hC).functor
  let t := reconstructionTwistData A C hC
  let U := pullbackUnitObj C.data hC t
  let u : PullbackHom C.data t U (F.obj A.data.tensorUnit) := fun g => (reconstructionUnitData A C hC g).hom
  let iX : PullbackHom C.data t (F.obj X) (F.obj X) := fun g => C.data.id (F.obj X g).val
  apply hom_ext_of_convolutionInclusions C.data hC t (F.obj X) U k
  intro a₀
  let a : SimpleOrbit A.toWeaklyPointedSuperfusion := a₀
  by_cases ha : a = k
  · have ha₀ : a₀ = k := ha
    subst a₀
    let D : C.data.Obj := (convolutionObj C.data hC t (F.obj X) U k).val
    let D' : C.data.Obj := (convolutionObj C.data hC t (F.obj X) (F.obj A.data.tensorUnit) k).val
    let P : C.data.Obj := (F.obj (A.data.tensorObj X A.data.tensorUnit) k).val
    let Z : C.data.Obj := (F.obj X k).val
    let L : C.data.Obj := twistSummand C.data t (F.obj X) U k (k⁻¹ * k)
    let L' : C.data.Obj := twistSummand C.data t (F.obj X) (F.obj A.data.tensorUnit) k (k⁻¹ * k)
    let R : C.data.Obj := (reconstructionComponentRealization A C hC k).obj
      (reconstructionTensorOutputSpan A X A.data.tensorUnit k k)
    let i : C.data.Hom L D := convolutionInclusion C.data hC t (F.obj X) U k k
    let i' : C.data.Hom L' D' := convolutionInclusion C.data hC t (F.obj X) (F.obj A.data.tensorUnit) k k
    let c : C.data.Hom D D' := convolutionHom C.data hC t iX u k
    let m : C.data.Hom D' P := (reconstructionTensoratorData A C hC X A.data.tensorUnit k).hom
    let n : C.data.Hom P Z := F.map (A.data.rightUnitorHom X) k
    let b : C.data.Hom L' R := (reconstructionConvolutionBlockIso A C hC X A.data.tensorUnit k k).hom.hom
    let j : C.data.Hom R P := (reconstructionMappedTensorBicone A C hC X A.data.tensorUnit k).ι k
    let v : C.data.Hom L L' := twistSummandHom C.data t iX u k (k⁻¹ * k)
    let q : C.data.Hom R Z := C.data.comp
      (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
        (congrArg (reconstructionComponentRealization A C hC k).obj
          (reconstructionRightUnitOutput_eq A X k))).hom
      ((reconstructionComponentRealization A C hC k).map (reconstructionRightUnitSpanMap A X k))
    let w : C.data.Hom L Z := (convolutionRightUnitBlockOfParity C.data hC t
      (reconstructionNu_one_right A C hC) (F.obj X) k).hom.hom
    let l : C.data.Hom D Z := (reconstructionRightUnitorData A C hC (F.obj X) k).hom
    have hc : C.data.comp i c = C.data.comp v i' := convolutionInclusion_map C.data hC t iX u k k
    have hm : C.data.comp i' m = C.data.comp b j := reconstructionTensorator_inclusion A C hC X A.data.tensorUnit k k
    have hn : C.data.comp j n = q := by
      have hh := reconstructionMappedRightUnitOutput_map A C hC X k
      rw [linear_eqToHom_eq_ofEq] at hh
      exact hh
    have hv : C.data.comp v (C.data.comp b q) = w := reconstructionRightUnitBlock_coherence A C hC X k
    have hl : C.data.comp i l = w := convolutionRightUnitor_inclusionOfParity C.data hC t
      (reconstructionNu_one_right A C hC) (F.obj X) k
    change C.data.comp i (C.data.comp (C.data.comp c m) n) = C.data.comp i l
    calc
      _ = C.data.comp (C.data.comp i c) (C.data.comp m n) :=
        (congrArg (C.data.comp i) (C.laws.comp_assoc c m n)).trans (C.laws.comp_assoc _ _ _).symm
      _ = C.data.comp (C.data.comp v i') (C.data.comp m n) := congrArg (fun z => C.data.comp z _) hc
      _ = C.data.comp v (C.data.comp (C.data.comp i' m) n) :=
        (C.laws.comp_assoc _ _ _).trans (congrArg (C.data.comp v) (C.laws.comp_assoc _ _ _).symm)
      _ = C.data.comp v (C.data.comp (C.data.comp b j) n) :=
        congrArg (fun z => C.data.comp v (C.data.comp z n)) hm
      _ = C.data.comp v (C.data.comp b (C.data.comp j n)) :=
        congrArg (C.data.comp v) (C.laws.comp_assoc _ _ _)
      _ = C.data.comp v (C.data.comp b q) := congrArg (fun z => C.data.comp v (C.data.comp b z)) hn
      _ = w := hv
      _ = _ := hl.symm
  · have hz : C.data.id (twistSummand C.data t (F.obj X) U a (a⁻¹ * k)) = C.data.zero := by
      have hu : a⁻¹ * k ≠ 1 := fun h => ha (inv_mul_eq_one.mp h)
      exact tensor_id_zero_left C.laws.toWeaklyPointedSuperfusionLaws
        (tensor_id_zero_right C.laws.toWeaklyPointedSuperfusionLaws (F.obj X a).val
          (pullbackUnit_id_zero C.data hC t (a⁻¹ * k) hu)) _
    exact (hom_eq_zero_of_source C.laws.toWeaklyPointedSuperfusionLaws hz _).trans
      (hom_eq_zero_of_source C.laws.toWeaklyPointedSuperfusionLaws hz _).symm

end RMod.Classification
