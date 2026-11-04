import RMod.Classification.Instances.ConvolutionScalarMap
import RMod.Classification.Proofs.ConvolutionInsertions

/-!
# The scalar convolution comparison is an even natural isomorphism

Cancelling the chosen biproduct comparison gives its exact value on each
inclusion. Scalars commute with arbitrary raw maps, so no homogeneity
restriction is needed for the naturality square.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (beta : t.group → t.group → ℝˣ)

theorem convolutionScalar_evenIso (X Y : PullbackObj C t) (k : t.group) :
    EvenIsoLaws C.toWeaklyPointedSuperfusionData (convolutionScalarData C hC t beta X Y k) :=
  evenIsoLaws_ofEvenIso ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
    (convolutionScalarEvenIso C hC t beta X Y k)

theorem convolutionScalarEvenIso_inclusion (X Y : PullbackObj C t) (k g : t.group) :
    convolutionInclusionEven C hC t X Y k g ≫
        (convolutionScalarEvenIso C hC t beta X Y k).hom =
      (convolutionScalarBlockEvenIso C hC t beta X Y k g).hom ≫
        convolutionInclusionEven C hC t X Y k g := by
  simp only [convolutionInclusionEven, convolutionScalarEvenIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc, biproduct.mapIso_hom,
    biproduct.ι_map_assoc]

theorem convolutionScalar_inclusion (X Y : PullbackObj C t) (k g : t.group) :
    C.comp (convolutionInclusion C hC t X Y k g)
      (convolutionScalarData C hC t beta X Y k).hom =
    C.smul (beta g (g⁻¹ * k)).val (convolutionInclusion C hC t X Y k g) := by
  have he := congrArg (fun f => f.hom) (convolutionScalarEvenIso_inclusion C hC t beta X Y k g)
  change C.comp (convolutionInclusion C hC t X Y k g)
      (convolutionScalarData C hC t beta X Y k).hom =
    C.comp (C.smul (beta g (g⁻¹ * k)).val (C.id _)) (convolutionInclusion C hC t X Y k g) at he
  exact he.trans ((hC.smul_comp _ _ _).trans (congrArg (C.smul _) (hC.id_comp _)))


theorem convolutionScalar_naturality {X X' Y Y' : PullbackObj C t}
    (f : PullbackHom C t X X') (q : PullbackHom C t Y Y') (k : t.group) :
    C.comp (convolutionHom C hC t f q k) (convolutionScalarData C hC t beta X' Y' k).hom =
      C.comp (convolutionScalarData C hC t beta X Y k).hom (convolutionHom C hC t f q k) := by
  apply hom_ext_of_convolutionInclusions C hC t X Y k
  intro g
  let i := convolutionInclusion C hC t X Y k g
  let i' := convolutionInclusion C hC t X' Y' k g
  let m := convolutionHom C hC t f q k
  let v := twistSummandHom C t f q g (g⁻¹ * k)
  let b := (convolutionScalarData C hC t beta X Y k).hom
  let b' := (convolutionScalarData C hC t beta X' Y' k).hom
  let r := (beta g (g⁻¹ * k)).val
  have hm : C.comp i m = C.comp v i' := convolutionInclusion_map C hC t f q k g
  have hb : C.comp i b = C.smul r i := convolutionScalar_inclusion C hC t beta X Y k g
  have hb' : C.comp i' b' = C.smul r i' := convolutionScalar_inclusion C hC t beta X' Y' k g
  change C.comp i (C.comp m b') = C.comp i (C.comp b m)
  calc
    _ = C.comp (C.comp i m) b' := (hC.comp_assoc _ _ _).symm
    _ = C.comp (C.comp v i') b' := congrArg (fun z => C.comp z b') hm
    _ = C.comp v (C.comp i' b') := hC.comp_assoc _ _ _
    _ = C.comp v (C.smul r i') := congrArg (C.comp v) hb'
    _ = C.smul r (C.comp v i') := hC.comp_smul _ _ _
    _ = C.smul r (C.comp i m) := congrArg (C.smul r) hm.symm
    _ = C.comp (C.smul r i) m := (hC.smul_comp _ _ _).symm
    _ = C.comp (C.comp i b) m := congrArg (fun z => C.comp z m) hb.symm
    _ = _ := hC.comp_assoc _ _ _

end RMod.Classification
