import RMod.Classification.Proofs.GaugeRightUnitBlockCoherence
import RMod.Classification.Proofs.GaugeTensoratorNaturality

/-!
# The gauge functor preserves the specified right convolution unitor

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

theorem gaugeTensorator_right_unit (hβ : ∀ g, d.beta g 1 = 1)
    (X : PullbackObj C s.data) (k : t.data.group) :
    C.comp (C.comp (convolutionHom C hC t.data
      (fun g => C.id (((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj X) g).val)
      (fun g => (gaugeUnitComponentData C hC s t d hρ hlam g).hom) k)
      (gaugeTensoratorData C hC s t d hρ hν X (pullbackUnitObj C hC s.data) k).hom)
      (C.tensorHom (convolutionRightUnitorData C hC s.data s.laws X (d.phi.symm k)).hom
        (C.id (C.pi.factor (d.lam (d.phi.symm k))))) =
    (convolutionRightUnitorData C hC t.data t.laws
      ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj X) k).hom := by
  classical
  let F := gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ
  let U := pullbackUnitObj C hC t.data
  let V := pullbackUnitObj C hC s.data
  let u : PullbackHom C t.data U (F.data.obj V) :=
    fun g => (gaugeUnitComponentData C hC s t d hρ hlam g).hom
  let iX : PullbackHom C t.data (F.data.obj X) (F.data.obj X) := fun g => C.id (F.data.obj X g).val
  apply hom_ext_of_convolutionInclusions C hC t.data (F.data.obj X) U k
  intro a
  by_cases ha : a = k
  · subst a
    let P := C.pi.factor (d.lam (d.phi.symm k))
    let D := (convolutionObj C hC t.data (F.data.obj X) U k).val
    let D' := (convolutionObj C hC t.data (F.data.obj X) (F.data.obj V) k).val
    let T := C.tensorObj (convolutionObj C hC s.data X V (d.phi.symm k)).val P
    let Z := (F.data.obj X k).val
    let L := twistSummand C t.data (F.data.obj X) U k (k⁻¹ * k)
    let L' := twistSummand C t.data (F.data.obj X) (F.data.obj V) k (k⁻¹ * k)
    let R := C.tensorObj (twistSummand C s.data X V (d.phi.symm k)
      ((d.phi.symm k)⁻¹ * d.phi.symm k)) P
    let i : C.Hom L D := convolutionInclusion C hC t.data (F.data.obj X) U k k
    let i' : C.Hom L' D' := convolutionInclusion C hC t.data (F.data.obj X) (F.data.obj V) k k
    let c : C.Hom D D' := convolutionHom C hC t.data iX u k
    let m : C.Hom D' T := (gaugeTensoratorData C hC s t d hρ hν X V k).hom
    let n : C.Hom T Z := C.tensorHom (convolutionRightUnitorData C hC s.data s.laws X (d.phi.symm k)).hom (C.id P)
    let b : C.Hom L' R := (gaugeTensorBlockData C hC s t d hρ hν X V k k).hom
    let j : C.Hom R T := C.tensorHom
      (convolutionInclusion C hC s.data X V (d.phi.symm k) (d.phi.symm k)) (C.id P)
    let v : C.Hom L L' := twistSummandHom C t.data iX u k (k⁻¹ * k)
    let q : C.Hom R Z := (gaugeRightUnitOutputData C hC s t d X k).hom
    let w : C.Hom L Z := (convolutionRightUnitBlock C hC t.data t.laws (F.data.obj X) k).hom.hom
    let l : C.Hom D Z := (convolutionRightUnitorData C hC t.data t.laws (F.data.obj X) k).hom
    have hc : C.comp i c = C.comp v i' := convolutionInclusion_map C hC t.data iX u k k
    have hm : C.comp i' m = C.comp b j := gaugeTensorator_inclusion C hC s t d hρ hν X V k k
    have hn : C.comp j n = q := gaugeRightUnitOutput_inclusion C hC s t d X k
    have hv : C.comp v (C.comp b q) = w := gaugeRightUnitBlock_coherence C hC s t d hρ hν hlam hβ X k
    have hl : C.comp i l = w := convolutionRightUnitor_inclusion C hC t.data t.laws (F.data.obj X) k
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
  · have hz : C.id (twistSummand C t.data (F.data.obj X) U a (a⁻¹ * k)) = C.zero :=
      tensor_id_zero_left hC.toWeaklyPointedSuperfusionLaws
        (tensor_id_zero_right hC.toWeaklyPointedSuperfusionLaws _
          (gaugeTargetUnit_zero C hC t (a⁻¹ * k)
            (fun he => ha (inv_mul_eq_one.mp he)))) _
    exact (hom_eq_zero_of_source hC.toWeaklyPointedSuperfusionLaws hz _).trans
      (hom_eq_zero_of_source hC.toWeaklyPointedSuperfusionLaws hz _).symm

end RMod.Classification
