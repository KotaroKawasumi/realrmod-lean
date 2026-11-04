import RMod.Classification.Proofs.ReconstructionTensoratorInsertions
import RMod.Classification.Proofs.ReconstructionTensorBlockNaturality
import RMod.Classification.Proofs.ReconstructionTensorPresentationNaturality
import RMod.Classification.Proofs.ConvolutionInsertions

/-!
# The global reconstruction tensorator is natural on every morphism

Convolution inclusions detect equality on the full Hom space. On each
summand, the desired square is the composite of convolution naturality,
the actual binary block square, and the mapped tensor-presentation
square. None of these steps restricts the input maps to even morphisms.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

theorem reconstructionTensorator_naturality (A C : PiSuperfusion.{0, 0})
    (hC : ReferenceProperty C.data) {X X' Y Y' : LinearCategory A.toWeaklyPointedSuperfusion}
    (f : X ⟶ X') (h : Y ⟶ Y') (k : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    C.data.comp (convolutionHom C.data hC (reconstructionTwistData A C hC)
      ((reconstructionUnderlyingEquivalence A C hC).functor.map f)
      ((reconstructionUnderlyingEquivalence A C hC).functor.map h) k)
      (reconstructionTensoratorData A C hC X' Y' k).hom =
    C.data.comp (reconstructionTensoratorData A C hC X Y k).hom
      ((reconstructionUnderlyingEquivalence A C hC).functor.map (A.data.tensorHom f h) k) := by
  let F := (reconstructionUnderlyingEquivalence A C hC).functor
  let t := reconstructionTwistData A C hC
  apply hom_ext_of_convolutionInclusions C.data hC t (F.obj X) (F.obj Y) k
  intro g₀
  let g : SimpleOrbit A.toWeaklyPointedSuperfusion := g₀
  let D : C.data.Obj := (convolutionObj C.data hC t (F.obj X) (F.obj Y) k).val
  let D' : C.data.Obj := (convolutionObj C.data hC t (F.obj X') (F.obj Y') k).val
  let P : C.data.Obj := (F.obj (A.data.tensorObj X Y) k).val
  let P' : C.data.Obj := (F.obj (A.data.tensorObj X' Y') k).val
  let L : C.data.Obj := twistSummand C.data t (F.obj X) (F.obj Y) g (g⁻¹ * k)
  let L' : C.data.Obj := twistSummand C.data t (F.obj X') (F.obj Y') g (g⁻¹ * k)
  let R : C.data.Obj := (reconstructionComponentRealization A C hC k).obj (reconstructionTensorOutputSpan A X Y k g)
  let R' : C.data.Obj := (reconstructionComponentRealization A C hC k).obj (reconstructionTensorOutputSpan A X' Y' k g)
  let i : C.data.Hom L D := convolutionInclusion C.data hC t (F.obj X) (F.obj Y) k g
  let i' : C.data.Hom L' D' := convolutionInclusion C.data hC t (F.obj X') (F.obj Y') k g
  let c : C.data.Hom D D' := convolutionHom C.data hC t (F.map f) (F.map h) k
  let u : C.data.Hom D P := (reconstructionTensoratorData A C hC X Y k).hom
  let u' : C.data.Hom D' P' := (reconstructionTensoratorData A C hC X' Y' k).hom
  let n : C.data.Hom P P' := F.map (A.data.tensorHom f h) k
  let b : C.data.Hom L R := (reconstructionConvolutionBlockIso A C hC X Y k g).hom.hom
  let b' : C.data.Hom L' R' := (reconstructionConvolutionBlockIso A C hC X' Y' k g).hom.hom
  let a : C.data.Hom L L' := twistSummandHom C.data t (F.map f) (F.map h) g (g⁻¹ * k)
  let q : C.data.Hom R R' := (reconstructionComponentRealization A C hC k).map
    (reconstructionTensorOutputSpanMap A f h k g)
  let j : C.data.Hom R P := (reconstructionMappedTensorBicone A C hC X Y k).ι g
  let j' : C.data.Hom R' P' := (reconstructionMappedTensorBicone A C hC X' Y' k).ι g
  have hc : C.data.comp i c = C.data.comp a i' := convolutionInclusion_map C.data hC t (F.map f) (F.map h) k g
  have hu' : C.data.comp i' u' = C.data.comp b' j' := reconstructionTensorator_inclusion A C hC X' Y' k g
  have hb : C.data.comp a b' = C.data.comp b q := reconstructionConvolutionBlockIso_naturality A C hC f h k g
  have hn : C.data.comp j n = C.data.comp q j' := reconstructionMappedTensorBicone_inclusion_naturality A C hC f h k g
  have hu : C.data.comp i u = C.data.comp b j := reconstructionTensorator_inclusion A C hC X Y k g
  change C.data.comp i (C.data.comp c u') = C.data.comp i (C.data.comp u n)
  calc
    _ = C.data.comp (C.data.comp i c) u' := (C.laws.comp_assoc _ _ _).symm
    _ = C.data.comp (C.data.comp a i') u' := congrArg (fun z => C.data.comp z u') hc
    _ = C.data.comp a (C.data.comp i' u') := C.laws.comp_assoc _ _ _
    _ = C.data.comp a (C.data.comp b' j') := congrArg (C.data.comp a) hu'
    _ = C.data.comp (C.data.comp a b') j' := (C.laws.comp_assoc _ _ _).symm
    _ = C.data.comp (C.data.comp b q) j' := congrArg (fun z => C.data.comp z j') hb
    _ = C.data.comp b (C.data.comp q j') := C.laws.comp_assoc _ _ _
    _ = C.data.comp b (C.data.comp j n) := congrArg (C.data.comp b) hn.symm
    _ = C.data.comp (C.data.comp b j) n := (C.laws.comp_assoc _ _ _).symm
    _ = C.data.comp (C.data.comp i u) n := congrArg (fun z => C.data.comp z n) hu.symm
    _ = _ := C.laws.comp_assoc _ _ _

end RMod.Classification
