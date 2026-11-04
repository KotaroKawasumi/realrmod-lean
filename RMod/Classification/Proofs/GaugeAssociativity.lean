import RMod.Classification.Proofs.GaugeProductTriple
import RMod.Classification.Proofs.GaugeProductLocalAssociativity
import RMod.Classification.Proofs.GaugeSourceAssociator
import RMod.Classification.Proofs.ConvolutionProductTripleExt
import RMod.Classification.Instances.GaugeMonoidalData

/-!
# Global associativity of the specified gauge tensorator

Test on every actual target triple insertion. The two binary routes,
the source and target associators, and the local gauge diagram have
already been identified with their specified maps. Naturality of the
output-index equality transports the right route. Cancelling that
equality comparison and using insertion extensionality proves the
complete diagram on arbitrary convolution objects.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace RMod.Classification

attribute [local implicit_reducible] twistSummand

theorem gaugeTensorator_associativity (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C)
    (s t : Twist) (d : GaugeData s.data t.data) (hd : GaugeLaws s.data t.data d) :
    let A := (twistedPullback C hC s).data.toWeaklyPointedSuperfusionData
    let B := (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData
    let F := gaugeMonoidalFunctorData C hC s t d hd.rho hd.nu hd.lam_one
    ∀ X Y Z,
      B.comp (B.comp (B.tensorHom (F.tensorHom X Y) (B.id (F.obj Z)))
        (F.tensorHom (A.tensorObj X Y) Z)) (F.map (A.associatorHom X Y Z)) =
      B.comp (B.comp (B.associatorHom (F.obj X) (F.obj Y) (F.obj Z))
        (B.tensorHom (B.id (F.obj X)) (F.tensorHom Y Z)))
        (F.tensorHom X (A.tensorObj Y Z)) := by
  dsimp only
  intro X Y Z
  let A : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  let F := gaugeUnderlyingFunctor C hC s t d.phi d.lam hd.rho
  let FX := F.data.obj X
  let FY := F.data.obj Y
  let FZ := F.data.obj Z
  let D := fun q => (convolutionObj C hC t.data (convolutionObj C hC t.data FX FY) FZ q).val
  let E := fun q => (convolutionObj C hC t.data FX (convolutionObj C hC t.data FY FZ) q).val
  let N := fun q => (F.data.obj (convolutionObj C hC s.data (convolutionObj C hC s.data X Y) Z) q).val
  let M := fun q => (F.data.obj (convolutionObj C hC s.data X (convolutionObj C hC s.data Y Z)) q).val
  let L : ∀ q, C.Hom (D q) (N q) := fun q => C.comp
    (convolutionHom C hC t.data (fun j => (gaugeTensoratorData C hC s t d hd.rho hd.nu X Y j).hom)
      (fun j => C.id (FZ j).val) q)
    (gaugeTensoratorData C hC s t d hd.rho hd.nu (convolutionObj C hC s.data X Y) Z q).hom
  let R : ∀ q, C.Hom (E q) (M q) := fun q => C.comp
    (convolutionHom C hC t.data (fun j => C.id (FX j).val)
      (fun j => (gaugeTensoratorData C hC s t d hd.rho hd.nu Y Z j).hom) q)
    (gaugeTensoratorData C hC s t d hd.rho hd.nu X (convolutionObj C hC s.data Y Z) q).hom
  let a : ∀ q, C.Hom (N q) (M q) := fun q => F.data.map
    (fun j => (convolutionAssociatorDataOfParity C hC s.data s.laws.normalizer_parity X Y Z j).hom) q
  let b : ∀ q, C.Hom (D q) (E q) := fun q =>
    (convolutionAssociatorDataOfParity C hC t.data t.laws.normalizer_parity FX FY FZ q).hom
  have main : (fun q => C.comp (L q) (a q)) = (fun q => C.comp (b q) (R q)) := by
    apply hom_ext_of_convolutionProductLeftInsertions C hC t.data FX FY FZ M
    intro g h k
    let u := (g * h) * k
    let v := g * (h * k)
    let z := (gaugeProductOutputTransportData C hC s t d X Y Z g h k).hom
    let zt := (IsoData.ofEq C.toWeaklyPointedSuperfusionData (congrArg E (mul_assoc g h k))).hom
    let iL := convolutionProductLeftInsertion C hC t.data FX FY FZ g h k
    let iR := convolutionProductRightInsertion C hC t.data FX FY FZ g h k
    let qL := (gaugeProductLeftLocalData C hC s t d hd.rho hd.nu X Y Z g h k).hom
    let qR := (gaugeProductRightLocalData C hC s t d hd.rho hd.nu X Y Z g h k).hom
    let jL := gaugeProductLeftSourceInsertion C hC s t d X Y Z g h k
    let jR := gaugeProductRightSourceInsertion C hC s t d X Y Z g h k
    let asrc := C.tensorHom (gaugeProductSourceAssociatorData C s t d X Y Z g h k).hom
      (C.id (C.pi.factor (d.lam (d.phi.symm u))))
    let esrc := (gaugeProductRightParityTransportData C s t d X Y Z g h k).hom
    let atgt := (C.pi.localAssociator (FX g).val (FY h).val (FZ k).val
      (t.data.nu g h) (t.data.nu (g * h) k) (t.data.nu h k) (t.data.nu g (h * k))
      (t.laws.normalizer_parity g h k) (t.data.omega g h k)).hom
    have hL : C.comp iL (L u) = C.comp qL jL :=
      gaugeTensorator_left_product_route C hC s t d hd.rho hd.nu X Y Z g h k
    have hR : C.comp iR (R v) = C.comp qR jR :=
      gaugeTensorator_right_product_route C hC s t d hd.rho hd.nu X Y Z g h k
    have hsrc : C.comp (C.comp jL (a u)) z = C.comp (C.comp asrc esrc) jR :=
      gaugeProductSourceInsertion_associator C hC s t d X Y Z g h k
    have hlocal : C.comp (C.comp qL asrc) esrc = C.comp atgt qR :=
      gaugeProductLocal_associativity C hC s t d hd.rho hd.nu hd.omega X Y Z g h k
    have htgt : C.comp (C.comp iL (b u)) zt = C.comp atgt iR :=
      convolutionProductInsertion_associator C hC t.data t.laws.normalizer_parity FX FY FZ g h k
    have hindex : C.comp (R u) z = C.comp zt (R v) :=
      indexed_morphism_eq_naturality A E M R (mul_assoc g h k) _ _
    change C.comp iL (C.comp (L u) (a u)) = C.comp iL (C.comp (b u) (R u))
    apply isoData_ofEq_cancel_right A (congrArg M (mul_assoc g h k))
    change C.comp (C.comp iL (C.comp (L u) (a u))) z =
      C.comp (C.comp iL (C.comp (b u) (R u))) z
    calc
      _ = C.comp (C.comp (C.comp iL (L u)) (a u)) z :=
        congrArg (fun q => C.comp q z) (hC.comp_assoc _ _ _).symm
      _ = C.comp (C.comp (C.comp qL jL) (a u)) z :=
        congrArg (fun q => C.comp (C.comp q (a u)) z) hL
      _ = C.comp qL (C.comp (C.comp jL (a u)) z) := by simp only [hC.comp_assoc]
      _ = C.comp qL (C.comp (C.comp asrc esrc) jR) := congrArg (C.comp qL) hsrc
      _ = C.comp (C.comp (C.comp qL asrc) esrc) jR := by simp only [hC.comp_assoc]
      _ = C.comp (C.comp atgt qR) jR := congrArg (fun q => C.comp q jR) hlocal
      _ = C.comp atgt (C.comp qR jR) := hC.comp_assoc _ _ _
      _ = C.comp atgt (C.comp iR (R v)) := congrArg (C.comp atgt) hR.symm
      _ = C.comp (C.comp atgt iR) (R v) := (hC.comp_assoc _ _ _).symm
      _ = C.comp (C.comp (C.comp iL (b u)) zt) (R v) :=
        congrArg (fun q => C.comp q (R v)) htgt.symm
      _ = C.comp (C.comp iL (b u)) (C.comp zt (R v)) := hC.comp_assoc _ _ _
      _ = C.comp (C.comp iL (b u)) (C.comp (R u) z) :=
        congrArg (C.comp (C.comp iL (b u))) hindex.symm
      _ = _ := by simp only [hC.comp_assoc]
  funext q
  exact (congrFun main q).trans (hC.comp_assoc _ _ _).symm

end RMod.Classification
