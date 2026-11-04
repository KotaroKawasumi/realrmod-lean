import RMod.Classification.Proofs.GaugeUnitBlockCoherence
import RMod.Classification.Proofs.GaugeTensoratorNaturality

/-!
# The gauge functor preserves the specified convolution unitors

Convolution inclusions detect equality on full Hom spaces. The only
nonzero unit summand is governed by the proved local unit equation;
all other summands have zero identity and hence only zero outgoing maps.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (d : GaugeData s.data t.data) (hρ : ∀ g, t.data.rho (d.phi g) = s.data.rho g)
  (hν : ∀ g h, t.data.nu (d.phi g) (d.phi h) =
    s.data.nu g h + d.lam h + d.lam (g * h) + d.lam g)
  (hlam : d.lam 1 = 0)

theorem gaugeTensorator_left_unit (hβ : ∀ g, d.beta 1 g = 1)
    (X : PullbackObj C s.data) (k : t.data.group) :
    C.comp (C.comp (convolutionHom C hC t.data
      (fun g => (gaugeUnitComponentData C hC s t d hρ hlam g).hom)
      (fun g => C.id (((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj X) g).val) k)
      (gaugeTensoratorData C hC s t d hρ hν (pullbackUnitObj C hC s.data) X k).hom)
      (C.tensorHom (convolutionLeftUnitorData C hC s.data s.laws X (d.phi.symm k)).hom
        (C.id (C.pi.factor (d.lam (d.phi.symm k))))) =
    (convolutionLeftUnitorData C hC t.data t.laws
      ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj X) k).hom := by
  classical
  let F := gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ
  let U := pullbackUnitObj C hC t.data
  let V := pullbackUnitObj C hC s.data
  let u : PullbackHom C t.data U (F.data.obj V) :=
    fun g => (gaugeUnitComponentData C hC s t d hρ hlam g).hom
  let iX : PullbackHom C t.data (F.data.obj X) (F.data.obj X) := fun g => C.id (F.data.obj X g).val
  apply hom_ext_of_convolutionInclusions C hC t.data U (F.data.obj X) k
  intro a
  by_cases ha : a = 1
  · subst a
    let P := C.pi.factor (d.lam (d.phi.symm k))
    let D := (convolutionObj C hC t.data U (F.data.obj X) k).val
    let D' := (convolutionObj C hC t.data (F.data.obj V) (F.data.obj X) k).val
    let T := C.tensorObj (convolutionObj C hC s.data V X (d.phi.symm k)).val P
    let Z := (F.data.obj X k).val
    let L := twistSummand C t.data U (F.data.obj X) 1 (1⁻¹ * k)
    let L' := twistSummand C t.data (F.data.obj V) (F.data.obj X) 1 (1⁻¹ * k)
    let R := C.tensorObj (twistSummand C s.data V X (d.phi.symm 1)
      ((d.phi.symm 1)⁻¹ * d.phi.symm k)) P
    let i : C.Hom L D := convolutionInclusion C hC t.data U (F.data.obj X) k 1
    let i' : C.Hom L' D' := convolutionInclusion C hC t.data (F.data.obj V) (F.data.obj X) k 1
    let c : C.Hom D D' := convolutionHom C hC t.data u iX k
    let m : C.Hom D' T := (gaugeTensoratorData C hC s t d hρ hν V X k).hom
    let n : C.Hom T Z := C.tensorHom (convolutionLeftUnitorData C hC s.data s.laws X (d.phi.symm k)).hom (C.id P)
    let b : C.Hom L' R := (gaugeTensorBlockData C hC s t d hρ hν V X k 1).hom
    let j : C.Hom R T := C.tensorHom
      (convolutionInclusion C hC s.data V X (d.phi.symm k) (d.phi.symm 1)) (C.id P)
    let v : C.Hom L L' := twistSummandHom C t.data u iX 1 (1⁻¹ * k)
    let q : C.Hom R Z := (gaugeLeftUnitOutputData C hC s t d X k).hom
    let w : C.Hom L Z := (convolutionLeftUnitBlock C hC t.data t.laws (F.data.obj X) k).hom.hom
    let l : C.Hom D Z := (convolutionLeftUnitorData C hC t.data t.laws (F.data.obj X) k).hom
    have hc : C.comp i c = C.comp v i' := convolutionInclusion_map C hC t.data u iX k 1
    have hm : C.comp i' m = C.comp b j := gaugeTensorator_inclusion C hC s t d hρ hν V X k 1
    have hn : C.comp j n = q := gaugeLeftUnitOutput_inclusion C hC s t d X k
    have hv : C.comp v (C.comp b q) = w := gaugeLeftUnitBlock_coherence C hC s t d hρ hν hlam hβ X k
    have hl : C.comp i l = w := convolutionLeftUnitor_inclusion C hC t.data t.laws (F.data.obj X) k
    change C.comp i (C.comp (C.comp c m) n) = C.comp i l
    calc
      _ = C.comp (C.comp i c) (C.comp m n) :=
        (congrArg (C.comp i) (hC.comp_assoc c m n)).trans (hC.comp_assoc _ _ _).symm
      _ = C.comp (C.comp v i') (C.comp m n) := congrArg (fun z => C.comp z _) hc
      _ = C.comp v (C.comp (C.comp i' m) n) :=
        (hC.comp_assoc _ _ _).trans (congrArg (C.comp v) (hC.comp_assoc _ _ _).symm)
      _ = C.comp v (C.comp (C.comp b j) n) := congrArg (fun z => C.comp v (C.comp z n)) hm
      _ = C.comp v (C.comp b (C.comp j n)) := congrArg (C.comp v) (hC.comp_assoc _ _ _)
      _ = C.comp v (C.comp b q) := congrArg (fun z => C.comp v (C.comp b z)) hn
      _ = w := hv
      _ = _ := hl.symm
  · have hz : C.id (twistSummand C t.data U (F.data.obj X) a (a⁻¹ * k)) = C.zero :=
      tensor_id_zero_left hC.toWeaklyPointedSuperfusionLaws
        (tensor_id_zero_left hC.toWeaklyPointedSuperfusionLaws
          (gaugeTargetUnit_zero C hC t a ha) _) _
    exact (hom_eq_zero_of_source hC.toWeaklyPointedSuperfusionLaws hz _).trans
      (hom_eq_zero_of_source hC.toWeaklyPointedSuperfusionLaws hz _).symm

end RMod.Classification
