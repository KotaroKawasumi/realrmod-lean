import RMod.Classification.Proofs.GaugeTensorator
import RMod.Classification.Proofs.ConvolutionInsertions

/-!
# Naturality of the global gauge tensorator on the complete Hom spaces

Test the square against every target convolution inclusion. Its block
square is local gauge naturality, followed by source convolution
naturality tensored with the identity of the output parity factor.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem gaugeTensorator_naturality
    (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
    (d : GaugeData s.data t.data) (hρ : ∀ g, t.data.rho (d.phi g) = s.data.rho g)
    (hν : ∀ g h, t.data.nu (d.phi g) (d.phi h) =
      s.data.nu g h + d.lam h + d.lam (g * h) + d.lam g)
    {X X' Y Y' : PullbackObj C s.data}
    (f : PullbackHom C s.data X X') (q : PullbackHom C s.data Y Y') (k : t.data.group) :
    C.comp (convolutionHom C hC t.data
      ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.map f)
      ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.map q) k)
      (gaugeTensoratorData C hC s t d hρ hν X' Y' k).hom =
    C.comp (gaugeTensoratorData C hC s t d hρ hν X Y k).hom
      ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.map
        (convolutionHom C hC s.data f q) k) := by
  let F := gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ
  apply hom_ext_of_convolutionInclusions C hC t.data (F.data.obj X) (F.data.obj Y) k
  intro l
  let D := (convolutionObj C hC t.data (F.data.obj X) (F.data.obj Y) k).val
  let D' := (convolutionObj C hC t.data (F.data.obj X') (F.data.obj Y') k).val
  let P := C.pi.factor (d.lam (d.phi.symm k))
  let T := C.tensorObj (convolutionObj C hC s.data X Y (d.phi.symm k)).val P
  let T' := C.tensorObj (convolutionObj C hC s.data X' Y' (d.phi.symm k)).val P
  let L := twistSummand C t.data (F.data.obj X) (F.data.obj Y) l (l⁻¹ * k)
  let L' := twistSummand C t.data (F.data.obj X') (F.data.obj Y') l (l⁻¹ * k)
  let R := C.tensorObj
    (twistSummand C s.data X Y (d.phi.symm l) ((d.phi.symm l)⁻¹ * d.phi.symm k)) P
  let R' := C.tensorObj
    (twistSummand C s.data X' Y' (d.phi.symm l) ((d.phi.symm l)⁻¹ * d.phi.symm k)) P
  let i : C.Hom L D := convolutionInclusion C hC t.data (F.data.obj X) (F.data.obj Y) k l
  let i' : C.Hom L' D' := convolutionInclusion C hC t.data (F.data.obj X') (F.data.obj Y') k l
  let c : C.Hom D D' := convolutionHom C hC t.data (F.data.map f) (F.data.map q) k
  let u : C.Hom D T := (gaugeTensoratorData C hC s t d hρ hν X Y k).hom
  let u' : C.Hom D' T' := (gaugeTensoratorData C hC s t d hρ hν X' Y' k).hom
  let n : C.Hom T T' := F.data.map (convolutionHom C hC s.data f q) k
  let a : C.Hom L L' := twistSummandHom C t.data (F.data.map f) (F.data.map q) l (l⁻¹ * k)
  let b : C.Hom L R := (gaugeTensorBlockData C hC s t d hρ hν X Y k l).hom
  let b' : C.Hom L' R' := (gaugeTensorBlockData C hC s t d hρ hν X' Y' k l).hom
  let m : C.Hom R R' := C.tensorHom
    (twistSummandHom C s.data f q (d.phi.symm l) ((d.phi.symm l)⁻¹ * d.phi.symm k)) (C.id P)
  let j : C.Hom R T := C.tensorHom
    (convolutionInclusion C hC s.data X Y (d.phi.symm k) (d.phi.symm l)) (C.id P)
  let j' : C.Hom R' T' := C.tensorHom
    (convolutionInclusion C hC s.data X' Y' (d.phi.symm k) (d.phi.symm l)) (C.id P)
  have hc : C.comp i c = C.comp a i' := convolutionInclusion_map C hC t.data _ _ k l
  have hu' : C.comp i' u' = C.comp b' j' := gaugeTensorator_inclusion C hC s t d hρ hν X' Y' k l
  have hb : C.comp a b' = C.comp b m := gaugeTensorBlock_naturality C hC s t d hρ hν f q k l
  have hn : C.comp j n = C.comp m j' := by
    change C.comp (C.tensorHom _ (C.id P)) (C.tensorHom _ (C.id P)) =
      C.comp (C.tensorHom _ (C.id P)) (C.tensorHom _ (C.id P))
    rw [interchange_second_even hC.toWeaklyPointedSuperfusionLaws _ _ _ _ (hC.id_even P),
      interchange_second_even hC.toWeaklyPointedSuperfusionLaws _ _ _ _ (hC.id_even P),
      convolutionInclusion_map]
  have hu : C.comp i u = C.comp b j := gaugeTensorator_inclusion C hC s t d hρ hν X Y k l
  change C.comp i (C.comp c u') = C.comp i (C.comp u n)
  calc
    _ = C.comp (C.comp i c) u' := (hC.comp_assoc _ _ _).symm
    _ = C.comp (C.comp a i') u' := congrArg (fun z => C.comp z u') hc
    _ = C.comp a (C.comp i' u') := hC.comp_assoc _ _ _
    _ = C.comp a (C.comp b' j') := congrArg (C.comp a) hu'
    _ = C.comp (C.comp a b') j' := (hC.comp_assoc _ _ _).symm
    _ = C.comp (C.comp b m) j' := congrArg (fun z => C.comp z j') hb
    _ = C.comp b (C.comp m j') := hC.comp_assoc _ _ _
    _ = C.comp b (C.comp j n) := congrArg (C.comp b) hn.symm
    _ = C.comp (C.comp b j) n := (hC.comp_assoc _ _ _).symm
    _ = C.comp (C.comp i u) n := congrArg (fun z => C.comp z n) hu.symm
    _ = _ := hC.comp_assoc _ _ _

end RMod.Classification
