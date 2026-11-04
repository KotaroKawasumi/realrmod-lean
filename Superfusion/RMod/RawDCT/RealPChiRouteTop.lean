import Superfusion.RMod.RawDCT.RealPChiRouteBridge

/-!
# Top-route soundness for the exact real pentagon kernel

This file identifies one semantic coordinate of the actual top pentagon
route with the corresponding executable integer kernel coefficient.  The
route-independent connector, fusion-slot, parity, and target-coordinate
bridges live in `RealPChiRouteBridge`.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiRouteTop

open GaugeChi
open Bimod
open RModCoordinate
open RealPChiKernel
open RealPChiRouteBridge
open scoped TensorProduct

/-! ## Association-insensitive numerical kernels -/

/-- The numerical right-slot kernel only reads the total label, so the two
parenthesizations used by the semantic target and the executable kernel
give literally the same integer. -/
theorem fusionRightSlotCoeff_assoc_label (a b c d : ZMod 8)
    (acting targetRow targetBasis sourceRow sourceBasis : ℕ) :
    fusionRightSlotCoeff a (b + (c + d)) acting targetRow targetBasis
        sourceRow sourceBasis =
      fusionRightSlotCoeff a (b + c + d) acting targetRow targetBasis
        sourceRow sourceBasis := by
  rw [← _root_.add_assoc b c d]

/-- Reindex the second connector's output coefficient basis back to the
left-associated total used by the executable fourfold kernel. -/
def topTotalBasisEquiv (a b c d : ZMod 8) :
    Fin (realRepDim (a + b + c + d).val) ≃
      Fin (realRepDim (a + (b + c) + d).val) :=
  finCongr (congrArg (fun x : ZMod 8 => realRepDim (x + d).val)
    (_root_.add_assoc a b c))

@[simp]
theorem topTotalBasisEquiv_val (a b c d : ZMod 8)
    (basis : Fin (realRepDim (a + b + c + d).val)) :
    (topTotalBasisEquiv a b c d basis).val = basis.val :=
  rfl

theorem topTotalBasisEquiv_eq_fusionBasisCastFst (a b c d : ZMod 8)
    (basis : Fin (realRepDim (a + b + c + d).val)) :
    topTotalBasisEquiv a b c d basis =
      fusionBasisCastFst d (_root_.add_assoc a b c) basis :=
  rfl

/-! ## Observation of the final right-slot action -/

/-- On the matching inner target frame, the native observation is exactly
one right fusion-slot coefficient of the outer column. -/
theorem semanticObserve_rightBasis (a b c d : ZMod 8)
    (target : QuadTarget a b c d)
    (acting : Fin (realRepDim (b + (c + d)).val))
    (sourceRow : FusionTable.Index a (b + c + d))
    (sourceBasis : Fin (coefficientRank (a + (b + c + d)))) :
    semanticObserve a b c d target
        (RelTensor.mk ℝ (realGauge.D (b + c + d)).carrier
          (GBR realGauge b c d)
          (FusionColumn (realGauge.fuse a (b + c + d)))
          (GBR.mk realGauge b c d
            (columnUnit c d target.1.1)
            (columnBasis b (c + d) target.1.2 acting))
          (columnBasis a (b + c + d) sourceRow sourceBasis)) =
      ((fusionRightSlotCoeff a (b + (c + d)) acting.val
        target.2.1.val target.2.2.val sourceRow.val sourceBasis.val : ℤ) : ℝ) := by
  rw [semanticObserve, GaugeChi.gq4NativeCoord_mk]
  rw [outerBasisCast]
  rw [show columnUnit c d target.1.1 =
      fsingle (realGauge.fuse c d)
        (FusionTable.frameIndex c d target.1.1) 1 from rfl]
  rw [show columnBasis b (c + d) target.1.2 acting =
      fsingle (realGauge.fuse b (c + d))
        (FusionTable.frameIndex b (c + d) target.1.2)
        (realRepBasis (b + (c + d)) acting) from rfl]
  rw [GaugeChi.gbrNativeColumnEquiv_fsingle]
  simp only [GaugeChi.fsingle_apply, if_true]
  let targetBasis' : Fin (realRepDim (a + (b + (c + d))).val) :=
    Fin.cast (congrArg (fun x : ZMod 8 => realRepDim x.val)
      (targetTotal_assoc a b c d)) target.2.2
  let sourceBasis' : Fin (realRepDim (a + (b + (c + d))).val) :=
    Fin.cast (congrArg (fun x : ZMod 8 => realRepDim x.val)
      (targetTotal_assoc a b c d)) sourceBasis
  have htarget : targetBasisNative a b c d target.2.2 = targetBasis' := rfl
  have hsource : targetBasisNative a b c d sourceBasis = sourceBasis' := rfl
  rw [hsource]
  rw [fusionRight_basis_apply]
  rw [map_sum]
  simp_rw [map_smul]
  rw [Finset.sum_eq_single targetBasis']
  · rw [← htarget, targetCoeffCoord_basis]
    simp
    rfl
  · intro other _ hne
    rw [targetCoeffCoord]
    change _ •
        (realRepBasis (a + (b + (c + d)))).coord
          (targetBasisNative a b c d target.2.2)
          (realRepBasis (a + (b + (c + d))) other) = 0
    rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply,
      if_neg (fun h => hne (h.trans htarget)), smul_zero]
  · exact fun h => absurd
      (Finset.mem_univ targetBasis') h

/-- An inner-frame basis generator outside the observed target frame has
zero native coordinate, independently of its outer column. -/
theorem semanticObserve_rightBasis_ne (a b c d : ZMod 8)
    (target : QuadTarget a b c d)
    (inner : TargetFrame b c d) (hinner : inner ≠ target.1)
    (acting : Fin (realRepDim (b + (c + d)).val))
    (sourceRow : FusionTable.Index a (b + c + d))
    (sourceBasis : Fin (coefficientRank (a + (b + c + d)))) :
    semanticObserve a b c d target
        (RelTensor.mk ℝ (realGauge.D (b + c + d)).carrier
          (GBR realGauge b c d)
          (FusionColumn (realGauge.fuse a (b + c + d)))
          (GBR.mk realGauge b c d
            (columnUnit c d inner.1)
            (columnBasis b (c + d) inner.2 acting))
          (columnBasis a (b + c + d) sourceRow sourceBasis)) = 0 := by
  rw [semanticObserve, GaugeChi.gq4NativeCoord_mk]
  rw [outerBasisCast]
  rw [show columnUnit c d inner.1 =
      fsingle (realGauge.fuse c d)
        (FusionTable.frameIndex c d inner.1) 1 from rfl]
  rw [show columnBasis b (c + d) inner.2 acting =
      fsingle (realGauge.fuse b (c + d))
        (FusionTable.frameIndex b (c + d) inner.2)
        (realRepBasis (b + (c + d)) acting) from rfl]
  rw [GaugeChi.gbrNativeColumnEquiv_fsingle]
  have hframe :
      GaugeChi.gbrNativeIndexEquiv ℝ realGauge b c d
          (FusionTable.frameIndex c d target.1.1,
            FusionTable.frameIndex b (c + d) target.1.2) ≠
        GaugeChi.gbrNativeIndexEquiv ℝ realGauge b c d
          (FusionTable.frameIndex c d inner.1,
            FusionTable.frameIndex b (c + d) inner.2) := by
    intro h
    apply hinner
    have hp := (GaugeChi.gbrNativeIndexEquiv ℝ realGauge b c d).injective h
    apply Prod.ext
    · exact (finSumFinEquiv.symm.injective (congrArg Prod.fst hp)).symm
    · exact (finSumFinEquiv.symm.injective (congrArg Prod.snd hp)).symm
  rw [GaugeChi.fsingle_apply, if_neg hframe]
  rw [zero_smul]
  change targetCoeffCoord a b c d target.2.2
      (0 : (realGauge.D (a + (b + (c + d)))).carrier) = 0
  exact map_zero (targetCoeffCoord a b c d target.2.2)

/-! ## The third edge, already paired with the target coordinate -/

/-- After observing the third edge, its target-frame sum collapses to the
selected inner frame.  The remaining coefficient-basis sum is exactly the
third connector coefficient followed by the final right fusion-slot
coefficient. -/
theorem semanticObserve_GE3_basis (a b c d : ZMod 8)
    (target : QuadTarget a b c d)
    (rowBC : FusionTable.Index b c)
    (rowBC_D : FusionTable.Index (b + c) d)
    (rowA_BCD : FusionTable.Index a (b + c + d))
    (basis3 : Fin (realRepDim (a + (b + c + d)).val)) :
    semanticObserve a b c d target
        (GaugeChi.GE3 ℝ realGauge a b c d
          (realRawConnectorFamily.T b c d)
          (realRawConnectorFamily.right_equivariance b c d)
          (RelTensor.mk ℝ (realGauge.D (b + c)).carrier
            (FusionColumn (realGauge.fuse b c))
            (GaugeChi.GQ3Inner ℝ realGauge a b c d)
            (columnUnit b c rowBC)
            (RelTensor.mk ℝ (realGauge.D (b + c + d)).carrier
              (FusionColumn (realGauge.fuse (b + c) d))
              (FusionColumn (realGauge.fuse a (b + c + d)))
              (columnUnit (b + c) d rowBC_D)
              (columnBasis a (b + c + d) rowA_BCD basis3)))) =
      ∑ basis4 : Fin (realRepDim (b + c + d).val),
        ((connectorLinearCoeff b c d
          target.1.1.val target.1.2.val rowBC.val rowBC_D.val
          basis4.val 0 : ℤ) : ℝ) *
        ((fusionRightSlotCoeff a (b + c + d) basis4.val
          target.2.1.val target.2.2.val rowA_BCD.val basis3.val : ℤ) : ℝ) := by
  rw [GaugeChi.GE3_mk]
  let outerMkW : GBR realGauge b c d →ₗ[ℝ]
      GaugeChi.GQ4 ℝ realGauge a b c d :=
    { toFun := fun m =>
        RelTensor.mk ℝ (realGauge.D (b + c + d)).carrier
          (GBR realGauge b c d)
          (FusionColumn (realGauge.fuse a (b + c + d))) m
          (columnBasis a (b + c + d) rowA_BCD basis3)
      map_add' := by
        intro x y
        rw [map_add, LinearMap.add_apply]
        rfl
      map_smul' := by
        intro r x
        rw [map_smul, LinearMap.smul_apply]
        rfl }
  change semanticObserve a b c d target
      (outerMkW
        (realRawConnectorFamily.T b c d
          (GBL.mk realGauge b c d
            (columnUnit b c rowBC)
            (columnUnit (b + c) d rowBC_D)))) = _
  let unitBasis : Fin (realRepDim (b + c + d).val) :=
    ⟨0, realRepDim_pos (b + c + d).val⟩
  have hunit : columnUnit (b + c) d rowBC_D =
      columnBasis (b + c) d rowBC_D unitBasis := by
    have hu : unitBasis = coefficientUnitIndex (b + c + d) := rfl
    rw [hu, columnBasis_unit_eq_columnUnit]
  rw [hunit]
  have hT := realRawConnector_on_basis_eq_sum_assoc b c d
    (rowBC, rowBC_D) unitBasis
  rw [hT]
  simp_rw [map_sum, map_smul]
  rw [Finset.sum_eq_single target.1]
  · apply Finset.sum_congr rfl
    intro basis4 _
    rw [show outerMkW
        (GBR.mk realGauge b c d
          (columnUnit c d target.1.1)
          (columnBasisAssoc b c d target.1.2 basis4)) =
        RelTensor.mk ℝ (realGauge.D (b + c + d)).carrier
          (GBR realGauge b c d)
          (FusionColumn (realGauge.fuse a (b + c + d)))
          (GBR.mk realGauge b c d
            (columnUnit c d target.1.1)
            (columnBasisAssoc b c d target.1.2 basis4))
          (columnBasis a (b + c + d) rowA_BCD basis3) from rfl]
    rw [columnBasisAssoc_eq]
    rw [semanticObserve_rightBasis]
    simp only [assocBasisEquiv, smul_eq_mul]
    have hunitVal : unitBasis.val = 0 := rfl
    simp only [finCongr_apply, Fin.val_cast]
    rw [hunitVal]
    rw [fusionRightSlotCoeff_assoc_label]
  · intro inner _ hinner
    apply Finset.sum_eq_zero
    intro basis4 _
    rw [show outerMkW
        (GBR.mk realGauge b c d
          (columnUnit c d inner.1)
          (columnBasisAssoc b c d inner.2 basis4)) =
        RelTensor.mk ℝ (realGauge.D (b + c + d)).carrier
          (GBR realGauge b c d)
          (FusionColumn (realGauge.fuse a (b + c + d)))
          (GBR.mk realGauge b c d
            (columnUnit c d inner.1)
            (columnBasisAssoc b c d inner.2 basis4))
          (columnBasis a (b + c + d) rowA_BCD basis3) from rfl]
    rw [columnBasisAssoc_eq]
    rw [semanticObserve_rightBasis_ne a b c d target inner hinner]
    simp
  · exact fun h => absurd (Finset.mem_univ target.1) h

/-! ## The middle connector and its preceding fusion slot -/

/-- The middle connector applied after the coefficient transported by the
first connector is the product of the left fusion-slot coefficient and the
second connector coefficient.  All associativity transports preserve the
underlying natural indices. -/
theorem realRawConnector_secondInput_eq_sum (a b c d : ZMod 8)
    (rowA_BC : FusionTable.Index a (b + c))
    (basis1 : Fin (realRepDim (a + b + c).val))
    (lastRow : FusionTable.Index (a + b + c) d)
    (sourceBasis : Fin (realRepDim (a + b + c + d).val)) :
    realRawConnectorFamily.T a (b + c) d
        (GBL.mk realGauge a (b + c) d
          (columnBasisAssoc a b c rowA_BC basis1)
          (GaugeChi.gColumnCastFst ℝ realGauge d (_root_.add_assoc a b c)
            (columnBasis (a + b + c) d lastRow sourceBasis))) =
      ∑ rowLast1 : FusionTable.Index (a + b + c) d,
        ∑ basis2 : Fin (realRepDim (a + b + c + d).val),
          ∑ target2 : TargetFrame a (b + c) d,
            ∑ basis3 : Fin (realRepDim (a + b + c + d).val),
              (((fusionLeftSlotCoeff (a + b + c) d basis1.val
                rowLast1.val basis2.val lastRow.val sourceBasis.val : ℤ) : ℝ) *
              ((connectorLinearCoeff a (b + c) d
                target2.1.val target2.2.val rowA_BC.val
                (fusionRowCastFst d (_root_.add_assoc a b c) rowLast1).val
                basis3.val
                (fusionBasisCastFst d (_root_.add_assoc a b c) basis2).val : ℤ) : ℝ)) •
                GBR.mk realGauge a (b + c) d
                  (columnUnit (b + c) d target2.1)
                  (columnBasisAssoc a (b + c) d target2.2
                    (topTotalBasisEquiv a b c d basis3)) := by
  rw [topSecondInput_eq_sum]
  simp_rw [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro rowLast1 _
  apply Finset.sum_congr rfl
  intro basis2 _
  have hT := realRawConnector_on_basis_eq_sum_assoc a (b + c) d
    (rowA_BC,
      fusionRowCastFst d (_root_.add_assoc a b c) rowLast1)
    (fusionBasisCastFst d (_root_.add_assoc a b c) basis2)
  rw [hT]
  simp_rw [Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro target2 _
  rw [← Equiv.sum_comp (topTotalBasisEquiv a b c d)]
  apply Finset.sum_congr rfl
  intro basis3 _
  rw [topTotalBasisEquiv_eq_fusionBasisCastFst]
  rfl

/-! ## The signed second edge followed by the observed third edge -/

/-- On one basis term emitted by the first connector, the last two top
edges evaluate to the five remaining finite sums.  The sign is still
written in the semantic `sgn` convention here; it is converted to the
kernel's `koszulSign` only in the route-level theorem. -/
theorem semanticObserve_GE3_GE2_basis (a b c d : ZMod 8)
    (target : QuadTarget a b c d)
    (rowBC : FusionTable.Index b c)
    (rowA_BC : FusionTable.Index a (b + c))
    (basis1 : Fin (realRepDim (a + b + c).val))
    (lastRow : FusionTable.Index (a + b + c) d)
    (sourceBasis : Fin (realRepDim (a + b + c + d).val)) :
    semanticObserve a b c d target
        (GaugeChi.GE3 ℝ realGauge a b c d
          (realRawConnectorFamily.T b c d)
          (realRawConnectorFamily.right_equivariance b c d)
          (GaugeChi.GE2 ℝ realGauge a b c d
            (GaugeChi.gParity ℝ realGauge a (b + c) d)
            (GaugeChi.gt2Canon ℝ realGauge a b c d
              (realRawConnectorFamily.equiv a (b + c) d)).toLinearMap
            (GaugeChi.gt2Canon_bcSlot ℝ realGauge
              (realRawConnectorFamily.equiv a (b + c) d)
              (GaugeChi.gParity ℝ realGauge a (b + c) d)
              (realRawConnectorFamily.mem_gParity a (b + c) d))
            (RelTensor.mk ℝ (realGauge.D (a + b + c)).carrier
              (GBR realGauge a b c)
              (FusionColumn (realGauge.fuse (a + b + c) d))
              (GBR.mk realGauge a b c
                (columnUnit b c rowBC)
                (columnBasisAssoc a b c rowA_BC basis1))
              (columnBasis (a + b + c) d lastRow sourceBasis)))) =
      ∑ rowLast1 : FusionTable.Index (a + b + c) d,
        ∑ basis2 : Fin (realRepDim (a + b + c + d).val),
          ∑ target2 : TargetFrame a (b + c) d,
            ∑ basis3 : Fin (realRepDim (a + b + c + d).val),
              ∑ basis4 : Fin (realRepDim (b + c + d).val),
                (((sgn ((GaugeChi.gParity ℝ realGauge a (b + c) d) *
                    FusionTable.indexParity b c rowBC) : ℤˣ) : ℤ) : ℝ) *
                  ((fusionLeftSlotCoeff (a + b + c) d basis1.val
                    rowLast1.val basis2.val lastRow.val sourceBasis.val : ℤ) : ℝ) *
                  ((connectorLinearCoeff a (b + c) d
                    target2.1.val target2.2.val rowA_BC.val rowLast1.val
                    basis3.val basis2.val : ℤ) : ℝ) *
                  ((connectorLinearCoeff b c d
                    target.1.1.val target.1.2.val rowBC.val target2.1.val
                    basis4.val 0 : ℤ) : ℝ) *
                  ((fusionRightSlotCoeff a (b + c + d) basis4.val
                    target.2.1.val target.2.2.val target2.2.val basis3.val : ℤ) : ℝ) := by
  rw [GaugeChi.GE2_mk_of_mem ℝ realGauge a b c d
    (GaugeChi.gParity ℝ realGauge a (b + c) d)
    (GaugeChi.gt2Canon ℝ realGauge a b c d
      (realRawConnectorFamily.equiv a (b + c) d)).toLinearMap
    (GaugeChi.gt2Canon_bcSlot ℝ realGauge
      (realRawConnectorFamily.equiv a (b + c) d)
      (GaugeChi.gParity ℝ realGauge a (b + c) d)
      (realRawConnectorFamily.mem_gParity a (b + c) d))
    (columnUnit_mem_grading b c rowBC)]
  let toInner : GBR realGauge a (b + c) d →ₗ[ℝ]
      GaugeChi.GQ3Inner ℝ realGauge a b c d :=
    { toFun := fun n => n
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let innerMk : GBR realGauge a (b + c) d →ₗ[ℝ]
      GaugeChi.GQ3 ℝ realGauge a b c d :=
    (RelTensor.mk ℝ (realGauge.D (b + c)).carrier
      (FusionColumn (realGauge.fuse b c))
      (GaugeChi.GQ3Inner ℝ realGauge a b c d)
      (columnUnit b c rowBC)).comp toInner
  change semanticObserve a b c d target
      (GaugeChi.GE3 ℝ realGauge a b c d
        (realRawConnectorFamily.T b c d)
        (realRawConnectorFamily.right_equivariance b c d)
        ((((sgn ((GaugeChi.gParity ℝ realGauge a (b + c) d) *
          FusionTable.indexParity b c rowBC) : ℤˣ) : ℤ)) •
          innerMk
            (GaugeChi.gt2Canon ℝ realGauge a b c d
              (realRawConnectorFamily.equiv a (b + c) d)
              (RelTensor.mk ℝ (realGauge.D (a + b + c)).carrier
                (FusionColumn (realGauge.fuse a (b + c)))
                (FusionColumn (realGauge.fuse (a + b + c) d))
                (columnBasisAssoc a b c rowA_BC basis1)
                (columnBasis (a + b + c) d lastRow sourceBasis))))) = _
  have hcanon := GaugeChi.gt2Canon_mk ℝ realGauge a b c d
    (realRawConnectorFamily.equiv a (b + c) d)
    (columnBasisAssoc a b c rowA_BC basis1)
    (columnBasis (a + b + c) d lastRow sourceBasis)
  rw [hcanon]
  rw [GaugeChi.ConnectorFamily.equiv_apply]
  rw [realRawConnector_secondInput_eq_sum]
  simp_rw [map_zsmul, map_sum, map_smul]
  have hinnerMk (target2 : TargetFrame a (b + c) d)
      (basis3 : Fin (realRepDim (a + b + c + d).val)) :
      innerMk
          (GBR.mk realGauge a (b + c) d
            (columnUnit (b + c) d target2.1)
            (columnBasisAssoc a (b + c) d target2.2
              (topTotalBasisEquiv a b c d basis3))) =
        RelTensor.mk ℝ (realGauge.D (b + c)).carrier
          (FusionColumn (realGauge.fuse b c))
          (GaugeChi.GQ3Inner ℝ realGauge a b c d)
          (columnUnit b c rowBC)
          (GBR.mk realGauge a (b + c) d
            (columnUnit (b + c) d target2.1)
            (columnBasisAssoc a (b + c) d target2.2
              (topTotalBasisEquiv a b c d basis3)) :
            GaugeChi.GQ3Inner ℝ realGauge a b c d) := rfl
  have hinnerInput (target2 : TargetFrame a (b + c) d)
      (basis3 : Fin (realRepDim (a + b + c + d).val)) :
      innerMk
          (GBR.mk realGauge a (b + c) d
            (columnUnit (b + c) d target2.1)
            (columnBasisAssoc a (b + c) d target2.2
              (topTotalBasisEquiv a b c d basis3))) =
        RelTensor.mk ℝ (realGauge.D (b + c)).carrier
          (FusionColumn (realGauge.fuse b c))
          (GaugeChi.GQ3Inner ℝ realGauge a b c d)
          (columnUnit b c rowBC)
          (RelTensor.mk ℝ (realGauge.D (b + c + d)).carrier
            (FusionColumn (realGauge.fuse (b + c) d))
            (FusionColumn (realGauge.fuse a (b + c + d)))
            (columnUnit (b + c) d target2.1)
            (columnBasis a (b + c + d) target2.2
              (assocBasisEquiv a (b + c) d
                (topTotalBasisEquiv a b c d basis3)))) := by
    rw [hinnerMk, columnBasisAssoc_eq]
    rfl
  have hObserve (target2 : TargetFrame a (b + c) d)
      (basis3 : Fin (realRepDim (a + b + c + d).val)) :
      semanticObserve a b c d target
          (GaugeChi.GE3 ℝ realGauge a b c d
            (realRawConnectorFamily.T b c d)
            (realRawConnectorFamily.right_equivariance b c d)
            (innerMk
              (GBR.mk realGauge a (b + c) d
                (columnUnit (b + c) d target2.1)
                (columnBasisAssoc a (b + c) d target2.2
                  (topTotalBasisEquiv a b c d basis3))))) =
        ∑ basis4 : Fin (realRepDim (b + c + d).val),
          ((connectorLinearCoeff b c d
            target.1.1.val target.1.2.val rowBC.val target2.1.val
            basis4.val 0 : ℤ) : ℝ) *
          ((fusionRightSlotCoeff a (b + c + d) basis4.val
            target.2.1.val target.2.2.val target2.2.val basis3.val : ℤ) : ℝ) := by
    rw [hinnerInput]
    rw [semanticObserve_GE3_basis]
    simp only [topTotalBasisEquiv_val, assocBasisEquiv,
      finCongr_apply, Fin.val_cast]
  simp_rw [hObserve]
  simp_rw [← Int.cast_smul_eq_zsmul ℝ]
  simp_rw [Finset.smul_sum, smul_eq_mul]
  simp only [fusionRowCastFst_val, fusionBasisCastFst_val]
  ring

/-! ## Removing the sparse short-circuit guards -/

/-- The zero tests in `topCoeff` are operational short-circuits only.
After expanding the finite ranges they equal the unguarded product of the
three connector entries and the two fusion-slot entries. -/
theorem topCoeff_eq_unguarded (a b c d : ZMod 8)
    (source : QuadSource a b c d) (target : QuadTarget a b c d) :
    topCoeff a b c d source target =
      ∑ rowBC : Fin (fusionRank b c),
        ∑ rowA_BC : Fin (fusionRank a (b + c)),
          ∑ basis1 : Fin (coefficientRank (a + b + c)),
            ∑ rowLast1 : Fin (fusionRank (a + b + c) d),
              ∑ basis2 : Fin (coefficientRank (a + b + c + d)),
                ∑ rowBC_D : Fin (fusionRank (b + c) d),
                  ∑ rowA_BCD : Fin (fusionRank a (b + c + d)),
                    ∑ basis3 : Fin (coefficientRank (a + b + c + d)),
                      ∑ basis4 : Fin (coefficientRank (b + c + d)),
                        connectorLinearCoeff a b c
                            rowBC.val rowA_BC.val source.1.1.val
                            source.1.2.val basis1.val 0 *
                          fusionLeftSlotCoeff (a + b + c) d basis1.val
                            rowLast1.val basis2.val source.2.1.val
                            source.2.2.val *
                          koszulSign
                            (connectorParityNat a (b + c) d *
                              rowParityNat b c rowBC.val) *
                          connectorLinearCoeff a (b + c) d
                            rowBC_D.val rowA_BCD.val rowA_BC.val
                            rowLast1.val basis3.val basis2.val *
                          connectorLinearCoeff b c d
                            target.1.1.val target.1.2.val rowBC.val
                            rowBC_D.val basis4.val 0 *
                          fusionRightSlotCoeff a (b + c + d) basis4.val
                            target.2.1.val target.2.2.val rowA_BCD.val
                            basis3.val := by
  unfold topCoeff
  simp_rw [sumRange_eq_sumFin]
  apply Finset.sum_congr rfl
  intro rowBC _
  apply Finset.sum_congr rfl
  intro rowA_BC _
  apply Finset.sum_congr rfl
  intro basis1 _
  by_cases h1 : connectorLinearCoeff a b c
      rowBC.val rowA_BC.val source.1.1.val source.1.2.val basis1.val
      0 = 0
  · rw [if_pos h1]
    simp [h1]
  · rw [if_neg h1]
    apply Finset.sum_congr rfl
    intro rowLast1 _
    apply Finset.sum_congr rfl
    intro basis2 _
    by_cases hslot : fusionLeftSlotCoeff (a + b + c) d basis1.val
        rowLast1.val basis2.val source.2.1.val source.2.2.val = 0
    · rw [if_pos hslot]
      simp [hslot]
    · rw [if_neg hslot]
      apply Finset.sum_congr rfl
      intro rowBC_D _
      apply Finset.sum_congr rfl
      intro rowA_BCD _
      apply Finset.sum_congr rfl
      intro basis3 _
      by_cases h2 : connectorLinearCoeff a (b + c) d
          rowBC_D.val rowA_BCD.val rowA_BC.val rowLast1.val
          basis3.val basis2.val = 0
      · rw [if_pos h2]
        simp [h2]
      · rw [if_neg h2]
        apply Finset.sum_congr rfl
        intro basis4 _
        by_cases h3 : connectorLinearCoeff b c d
            target.1.1.val target.1.2.val rowBC.val rowBC_D.val
            basis4.val 0 = 0
        · rw [if_pos h3]
          simp [h3]
        · rw [if_neg h3]

/-! ## Full top-route soundness -/

/-- The native target coordinate of the actual semantic top route is the
cast of the executable integer coefficient `topCoeff`.  No fourfold table
is recomputed: the proof composes the three stored connector tables with
the two stored fusion-slot tables. -/
theorem semanticObserve_famTop (a b c d : ZMod 8)
    (source : QuadSource a b c d) (target : QuadTarget a b c d) :
    semanticObserve a b c d target
        (GaugeChi.famTop ℝ realGauge realRawConnectorFamily
          a b c d (semanticSource a b c d source)) =
      ((topCoeff a b c d source target : ℤ) : ℝ) := by
  let sourceBasisRaw : Fin (realRepDim (a + b + c + d).val) :=
    source.2.2
  have hsourceBasis : sourceBasisRaw = source.2.2 := rfl
  let unitBasis1 : Fin (realRepDim (a + b + c).val) :=
    ⟨0, realRepDim_pos (a + b + c).val⟩
  have hunit1 : columnUnit (a + b) c source.1.2 =
      columnBasis (a + b) c source.1.2 unitBasis1 := by
    have hu : unitBasis1 = coefficientUnitIndex (a + b + c) := rfl
    rw [hu, columnBasis_unit_eq_columnUnit]
  have h1 := realRawConnector_on_basis_eq_sum_assoc a b c
    source.1 unitBasis1
  let q2MkW : GBR realGauge a b c →ₗ[ℝ]
      GaugeChi.GQ2 ℝ realGauge a b c d :=
    { toFun := fun m =>
        RelTensor.mk ℝ (realGauge.D (a + b + c)).carrier
          (GBR realGauge a b c)
          (FusionColumn (realGauge.fuse (a + b + c) d)) m
          (columnBasis (a + b + c) d source.2.1 sourceBasisRaw)
      map_add' := by
        intro x y
        rw [map_add, LinearMap.add_apply]
        rfl
      map_smul' := by
        intro r x
        rw [map_smul, LinearMap.smul_apply]
        rfl }
  let middle2 (middle : TargetFrame a b c)
      (basis1 : Fin (realRepDim (a + b + c).val)) :
      GaugeChi.GQ2 ℝ realGauge a b c d :=
    q2MkW
      (GBR.mk realGauge a b c
        (columnUnit b c middle.1)
        (columnBasisAssoc a b c middle.2 basis1))
  have h1lift :
      q2MkW
        (realRawConnectorFamily.T a b c
            (GBL.mk realGauge a b c
              (columnUnit a b source.1.1)
              (columnBasis (a + b) c source.1.2 unitBasis1))) =
        ∑ middle : TargetFrame a b c,
          ∑ basis1 : Fin (realRepDim (a + b + c).val),
            ((connectorLinearCoeff a b c
              middle.1.val middle.2.val source.1.1.val source.1.2.val
              basis1.val 0 : ℤ) : ℝ) •
              middle2 middle basis1 := by
    rw [h1]
    simp_rw [map_sum, map_smul]
    simp only [unitBasis1]
    rfl
  have hGE1 :
      GaugeChi.GE1 ℝ realGauge a b c d
          (realRawConnectorFamily.T a b c)
          (realRawConnectorFamily.right_equivariance a b c)
          (semanticSource a b c d source) =
        ∑ middle : TargetFrame a b c,
          ∑ basis1 : Fin (realRepDim (a + b + c).val),
            ((connectorLinearCoeff a b c
              middle.1.val middle.2.val source.1.1.val source.1.2.val
              basis1.val 0 : ℤ) : ℝ) •
              middle2 middle basis1 := by
    rw [semanticSource, GaugeChi.GE1_mk]
    rw [hunit1]
    rw [← hsourceBasis]
    change q2MkW
      (realRawConnectorFamily.T a b c
        (GBL.mk realGauge a b c
          (columnUnit a b source.1.1)
          (columnBasis (a + b) c source.1.2 unitBasis1))) = _
    exact h1lift
  have hTail (middle : TargetFrame a b c)
      (basis1 : Fin (realRepDim (a + b + c).val)) :
      semanticObserve a b c d target
          (GaugeChi.GE3 ℝ realGauge a b c d
            (realRawConnectorFamily.T b c d)
            (realRawConnectorFamily.right_equivariance b c d)
            (GaugeChi.GE2 ℝ realGauge a b c d
              (GaugeChi.gParity ℝ realGauge a (b + c) d)
              (GaugeChi.gt2Canon ℝ realGauge a b c d
                (realRawConnectorFamily.equiv a (b + c) d)).toLinearMap
              (GaugeChi.gt2Canon_bcSlot ℝ realGauge
                (realRawConnectorFamily.equiv a (b + c) d)
                (GaugeChi.gParity ℝ realGauge a (b + c) d)
                (realRawConnectorFamily.mem_gParity a (b + c) d))
              (middle2 middle basis1))) =
        ∑ rowLast1 : FusionTable.Index (a + b + c) d,
          ∑ basis2 : Fin (realRepDim (a + b + c + d).val),
            ∑ target2 : TargetFrame a (b + c) d,
              ∑ basis3 : Fin (realRepDim (a + b + c + d).val),
                ∑ basis4 : Fin (realRepDim (b + c + d).val),
                  (((sgn ((GaugeChi.gParity ℝ realGauge a (b + c) d) *
                      FusionTable.indexParity b c middle.1) : ℤˣ) : ℤ) : ℝ) *
                    ((fusionLeftSlotCoeff (a + b + c) d basis1.val
                      rowLast1.val basis2.val source.2.1.val
                      sourceBasisRaw.val : ℤ) : ℝ) *
                    ((connectorLinearCoeff a (b + c) d
                      target2.1.val target2.2.val middle.2.val
                      rowLast1.val basis3.val basis2.val : ℤ) : ℝ) *
                    ((connectorLinearCoeff b c d
                      target.1.1.val target.1.2.val middle.1.val
                      target2.1.val basis4.val 0 : ℤ) : ℝ) *
                    ((fusionRightSlotCoeff a (b + c + d) basis4.val
                      target.2.1.val target.2.2.val target2.2.val
                      basis3.val : ℤ) : ℝ) := by
    unfold middle2
    exact semanticObserve_GE3_GE2_basis a b c d target
      middle.1 middle.2 basis1 source.2.1 sourceBasisRaw
  have hsign (rowBC : FusionTable.Index b c) :
      ((((sgn ((GaugeChi.gParity ℝ realGauge a (b + c) d) *
        FusionTable.indexParity b c rowBC) : ℤˣ) : ℤ) : ℝ)) =
        ((koszulSign
          (connectorParityNat a (b + c) d *
            rowParityNat b c rowBC.val) : ℤ) : ℝ) := by
    rw [semanticSign_eq_koszulSign]
    rw [← congrArg ZMod.val (rawParity_eq_gParity a (b + c) d)]
    rw [← rowParityNat_eq_indexParity_val b c rowBC]
    rfl
  change semanticObserve a b c d target
      (GaugeChi.GE3 ℝ realGauge a b c d
        (realRawConnectorFamily.T b c d)
        (realRawConnectorFamily.right_equivariance b c d)
        (GaugeChi.GE2 ℝ realGauge a b c d
          (GaugeChi.gParity ℝ realGauge a (b + c) d)
          (GaugeChi.gt2Canon ℝ realGauge a b c d
            (realRawConnectorFamily.equiv a (b + c) d)).toLinearMap
          (GaugeChi.gt2Canon_bcSlot ℝ realGauge
            (realRawConnectorFamily.equiv a (b + c) d)
            (GaugeChi.gParity ℝ realGauge a (b + c) d)
            (realRawConnectorFamily.mem_gParity a (b + c) d))
          (GaugeChi.GE1 ℝ realGauge a b c d
            (realRawConnectorFamily.T a b c)
            (realRawConnectorFamily.right_equivariance a b c)
            (semanticSource a b c d source)))) = _
  rw [hGE1]
  simp_rw [map_sum, map_smul]
  simp_rw [hTail]
  simp_rw [Finset.smul_sum, smul_eq_mul]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [hsign]
  rw [topCoeff_eq_unguarded]
  push_cast
  apply Finset.sum_congr rfl
  intro rowBC _
  apply Finset.sum_congr rfl
  intro rowA_BC _
  apply Finset.sum_congr rfl
  intro basis1 _
  apply Finset.sum_congr rfl
  intro rowLast1 _
  apply Finset.sum_congr rfl
  intro basis2 _
  apply Finset.sum_congr rfl
  intro rowBC_D _
  apply Finset.sum_congr rfl
  intro rowA_BCD _
  apply Finset.sum_congr rfl
  intro basis3 _
  apply Finset.sum_congr rfl
  intro basis4 _
  simp only [sourceBasisRaw]
  ring

end RealPChiRouteTop
end Superfusion.RMod.RawDCT
