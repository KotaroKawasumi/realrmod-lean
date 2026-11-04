import RMod.Classification.Proofs.GaugeUnitBlockCoherence

/-!
# The surviving right unit block of the gauge functor

The complementary target index is the identity. After retaining its
index equality and the source equality maps, the diagram is exactly
the already checked right unit diagram for the local tensorator.
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

theorem gaugeRightUnitBlock_coherence (hβ : ∀ g, d.beta g 1 = 1)
    (X : PullbackObj C s.data) (k : t.data.group) :
    C.comp (twistSummandHom C t.data
      (fun j => C.id (((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj X) j).val)
      (fun j => (gaugeUnitComponentData C hC s t d hρ hlam j).hom)
      k (k⁻¹ * k))
      (C.comp (gaugeTensorBlockData C hC s t d hρ hν X (pullbackUnitObj C hC s.data) k k).hom
        (gaugeRightUnitOutputData C hC s t d X k).hom) =
      (convolutionRightUnitBlock C hC t.data t.laws
        ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj X) k).hom.hom := by
  classical
  let F := gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ
  have hs : twistSummand C s.data X (pullbackUnitObj C hC s.data) (d.phi.symm k)
      ((d.phi.symm k)⁻¹ * d.phi.symm k) =
      C.tensorObj (C.tensorObj (X (d.phi.symm k)).val C.tensorUnit) C.tensorUnit := by
    change C.tensorObj (C.tensorObj (X (d.phi.symm k)).val
      ((fun j => (pullbackUnitObj C hC s.data j).val) ((d.phi.symm k)⁻¹ * d.phi.symm k)))
      (C.pi.factor (s.data.nu (d.phi.symm k) ((d.phi.symm k)⁻¹ * d.phi.symm k))) = _
    rw [inv_mul_cancel, s.laws.nu_one_right]
    dsimp only
    rw [pullbackUnitObj, supportedObj_one]
    rfl
  have ht : twistSummand C t.data (F.data.obj X) (pullbackUnitObj C hC t.data) k
      (k⁻¹ * k) = C.tensorObj (C.tensorObj (F.data.obj X k).val C.tensorUnit) C.tensorUnit := by
    change C.tensorObj (C.tensorObj (F.data.obj X k).val
      ((fun j => (pullbackUnitObj C hC t.data j).val) (k⁻¹ * k)))
      (C.pi.factor (t.data.nu k (k⁻¹ * k))) = _
    rw [inv_mul_cancel, t.laws.nu_one_right]
    dsimp only
    rw [pullbackUnitObj, supportedObj_one]
    rfl
  dsimp only [gaugeTensorBlockData, gaugeRightUnitOutputData, twistSummandHom,
    convolutionRightUnitBlock, IsoData.trans, IsoData.tensor, IsoData.ofEvenIso]
  rw [convolutionRightUnitBlockOfParity_hom C hC s.data s.laws.nu_one_right X
      (d.phi.symm k) hs,
    convolutionRightUnitBlockOfParity_hom C hC t.data t.laws.nu_one_right (F.data.obj X) k ht]
  simp only [gaugeUnitComponentData, dif_pos (inv_mul_cancel k)]
  dsimp only [gaugeUnderlyingFunctor, gaugeUnderlyingFunctorData,
    IsoData.trans, IsoData.symm, IsoData.rightUnit, IsoData.refl,
    pullbackUnitObj, supportedObj]
  -- Reduce the indices under arbitrary equality witnesses, preserving the original maps.
  generalize_proofs hFX hu hFU heU heF hi hepar hecomp
  revert heU heF hi hepar hecomp hs ht
  dsimp only [F, gaugeUnderlyingFunctor, gaugeUnderlyingFunctorData,
    twistSummand, pullbackUnitObj, supportedObj]
  rw! [inv_mul_cancel k]
  intro hs ht heU heF hi
  cases hi
  dsimp only
  revert hs ht heU heF
  rw! [map_one d.phi.symm, inv_mul_cancel (d.phi.symm k),
    hlam, s.laws.nu_one_right (d.phi.symm k), t.laws.nu_one_right k]
  rw! [show (if (1 : s.data.group) = 1 then C.tensorUnit else
      (pullbackZeroObj C hC s.data 1).val) = C.tensorUnit from if_pos rfl,
    show (if (1 : t.data.group) = 1 then C.tensorUnit else
      (pullbackZeroObj C hC t.data 1).val) = C.tensorUnit from if_pos rfl]
  simp only [hβ]
  intros
  simp only [IsoData.ofEq, IsoData.refl, hC.id_comp, hC.comp_id]
  -- The inherited ring and field instances of ZMod have the same zero.
  with_unfolding_all exact (gaugeLocalTensorator_right_unit
    ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩ C.pi hC.pi
    (X (d.phi.symm k)).val (d.lam (d.phi.symm k)))

end RMod.Classification
