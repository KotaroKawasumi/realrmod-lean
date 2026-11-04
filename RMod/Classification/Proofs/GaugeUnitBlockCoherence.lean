import RMod.Classification.Proofs.GaugeLocalUnitMaps
import RMod.Classification.Proofs.GaugeUnitOutput
import RMod.Classification.Proofs.GaugeUnit
import RMod.Classification.Proofs.ConvolutionUnitBlockFormula
import Batteries.Tactic.GeneralizeProofs
import Mathlib.Tactic.DepRewrite

/-!
# The gauge unit diagrams on their surviving convolution blocks

The index and supported-unit equality maps are retained when applying the
local unit equations. Normalization of lambda and beta gives precisely
the canonical unit comparison and the scalar-free local tensorator.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace RMod.Classification

attribute [local implicit_reducible] PiData.factor

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (d : GaugeData s.data t.data) (hρ : ∀ g, t.data.rho (d.phi g) = s.data.rho g)
  (hν : ∀ g h, t.data.nu (d.phi g) (d.phi h) =
    s.data.nu g h + d.lam h + d.lam (g * h) + d.lam g)
  (hlam : d.lam 1 = 0)

theorem gaugeLeftUnitBlock_coherence (hβ : ∀ g, d.beta 1 g = 1)
    (X : PullbackObj C s.data) (k : t.data.group) :
    C.comp (twistSummandHom C t.data
      (fun j => (gaugeUnitComponentData C hC s t d hρ hlam j).hom)
      (fun j => C.id (((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj X) j).val)
      1 (1⁻¹ * k))
      (C.comp (gaugeTensorBlockData C hC s t d hρ hν (pullbackUnitObj C hC s.data) X k 1).hom
        (gaugeLeftUnitOutputData C hC s t d X k).hom) =
      (convolutionLeftUnitBlock C hC t.data t.laws
        ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj X) k).hom.hom := by
  classical
  let F := gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ
  have hs : twistSummand C s.data (pullbackUnitObj C hC s.data) X 1
      (1⁻¹ * d.phi.symm k) =
      C.tensorObj (C.tensorObj C.tensorUnit (X (d.phi.symm k)).val) C.tensorUnit := by
    change C.tensorObj (C.tensorObj (pullbackUnitObj C hC s.data 1).val
      ((fun j => (X j).val) (1⁻¹ * d.phi.symm k))) (C.pi.factor (s.data.nu 1 (1⁻¹ * d.phi.symm k))) = _
    have he : (1 : s.data.group)⁻¹ * d.phi.symm k = d.phi.symm k := by simp
    rw [he, s.laws.nu_one_left, pullbackUnitObj, supportedObj_one]
    rfl
  have ht : twistSummand C t.data (pullbackUnitObj C hC t.data) (F.data.obj X) 1
      (1⁻¹ * k) = C.tensorObj (C.tensorObj C.tensorUnit (F.data.obj X k).val) C.tensorUnit := by
    change C.tensorObj (C.tensorObj (pullbackUnitObj C hC t.data 1).val
      ((fun j => (F.data.obj X j).val) (1⁻¹ * k))) (C.pi.factor (t.data.nu 1 (1⁻¹ * k))) = _
    have he : (1 : t.data.group)⁻¹ * k = k := by simp
    rw [he, t.laws.nu_one_left, pullbackUnitObj, supportedObj_one]
    rfl
  dsimp only [gaugeTensorBlockData, gaugeLeftUnitOutputData, twistSummandHom,
    convolutionLeftUnitBlock, IsoData.trans, IsoData.tensor, IsoData.ofEvenIso]
  rw [convolutionLeftUnitBlockOfParity_hom C hC s.data s.laws.nu_one_left X
      (d.phi.symm k) hs,
    convolutionLeftUnitBlockOfParity_hom C hC t.data t.laws.nu_one_left (F.data.obj X) k ht]
  simp only [gaugeUnitComponentData, dite_true]
  dsimp only [gaugeUnderlyingFunctor, gaugeUnderlyingFunctorData,
    IsoData.trans, IsoData.symm, IsoData.rightUnit, IsoData.refl,
    pullbackUnitObj, supportedObj]
  -- Reduce the indices under arbitrary equality witnesses, preserving the original maps.
  generalize_proofs hu hFX hFU heU heF hepar hecomp heidx
  revert heU heF hepar hecomp heidx hs ht
  dsimp only [F, gaugeUnderlyingFunctor, gaugeUnderlyingFunctorData,
    twistSummand, pullbackUnitObj, supportedObj]
  rw! [show (1 : t.data.group)⁻¹ * k = k by simp,
    map_one d.phi.symm,
    show (1 : s.data.group)⁻¹ * d.phi.symm k = d.phi.symm k by simp,
    hlam, s.laws.nu_one_left (d.phi.symm k), t.laws.nu_one_left k]
  rw! [show (if (1 : s.data.group) = 1 then C.tensorUnit else
      (pullbackZeroObj C hC s.data 1).val) = C.tensorUnit from if_pos rfl,
    show (if (1 : t.data.group) = 1 then C.tensorUnit else
      (pullbackZeroObj C hC t.data 1).val) = C.tensorUnit from if_pos rfl]
  simp only [hβ]
  intros
  simp only [IsoData.ofEq, IsoData.refl, hC.id_comp, hC.comp_id]
  -- The inherited ring and field instances of ZMod have the same zero.
  with_unfolding_all exact
    (gaugeLocalTensorator_left_unit
      ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩ C.pi hC.pi
      (X (d.phi.symm k)).val (d.lam (d.phi.symm k)))

end RMod.Classification
