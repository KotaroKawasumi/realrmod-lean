import Superfusion.RMod.RawDCT.RealPChiRouteBridge

/-!
# Bottom-route soundness for the exact real pentagon kernel

This file identifies one semantic coordinate of the actual bottom pentagon
route with the corresponding executable integer kernel coefficient.  The
proof follows the two raw connectors in `GE4` and `GE5`; the closing map is
only an associativity recast and contributes no numerical coefficient.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiRouteBottom

open GaugeChi
open Bimod
open RModCoordinate
open RealPChiKernel
open RealPChiRouteBridge
open scoped TensorProduct

/-! ## The two bottom-route Koszul signs -/

/-- The two semantic `ZMod 2` signs are exactly the product of the two
integer signs used by the executable bottom kernel.  This is a sixteen-case
identity of parity bits, independent of all group labels and tables. -/
theorem semanticBottomSign_eq_koszulSigns (p q r s : ZMod 2) :
    ((((sgn (p * q) : ℤˣ) : ℤ) : ℝ)) *
        ((((sgn (r * (s + q)) : ℤˣ) : ℤ) : ℝ)) =
      ((koszulSign (p.val * q.val) *
        koszulSign (r.val * (s.val + q.val)) : ℤ) : ℝ) := by
  have hone : (1 : ZMod 2) + 1 = 0 := by decide
  rcases zmod2_cases p with hp | hp <;> subst p
  all_goals rcases zmod2_cases q with hq | hq <;> subst q
  all_goals rcases zmod2_cases r with hr | hr <;> subst r
  all_goals rcases zmod2_cases s with hs | hs <;> subst s
  all_goals simp [koszulSign, Superfusion.sgn, ZMod.val_one, hone]

/-! ## Exact observation after the closing reassociation -/

/-- Equality of native right-frame positions is exactly componentwise
equality of the two raw binary rows. -/
private theorem nativeRightFrame_eq_iff (x y z : ZMod 8)
    (r r' : FusionTable.Index y z)
    (s s' : FusionTable.Index x (y + z)) :
    gbrNativeIndexEquiv ℝ realGauge x y z
        (FusionTable.frameIndex y z r,
          FusionTable.frameIndex x (y + z) s) =
      gbrNativeIndexEquiv ℝ realGauge x y z
        (FusionTable.frameIndex y z r',
          FusionTable.frameIndex x (y + z) s') ↔
        r = r' ∧ s = s' := by
  constructor
  · intro h
    have hp := (gbrNativeIndexEquiv ℝ realGauge x y z).injective h
    constructor
    · exact finSumFinEquiv.symm.injective (congrArg Prod.fst hp)
    · exact finSumFinEquiv.symm.injective (congrArg Prod.snd hp)
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A closed native generator is a Kronecker delta in the four stored
target coordinates.  This is the sign-free endpoint calculation shared by
all terms of the second connector expansion. -/
theorem semanticObserve_close_exact (a b c d : ZMod 8)
    (target : QuadTarget a b c d)
    (rowCD : FusionTable.Index c d)
    (rowBCD : FusionTable.Index b (c + d))
    (rowLast : FusionTable.Index a (b + (c + d)))
    (basis : Fin (realRepDim (a + b + (c + d)).val)) :
    semanticObserve a b c d target
        ((gq4Close ℝ realGauge a b c d).toLinearMap
          (RelTensor.mk ℝ (realGauge.D (c + d)).carrier
            (FusionColumn (realGauge.fuse c d))
            (GBR realGauge a b (c + d))
            (columnUnit c d rowCD)
            (GBR.mk realGauge a b (c + d)
              (columnUnit b (c + d) rowBCD)
              (columnBasisAssoc a b (c + d) rowLast basis)))) =
      if rowCD = target.1.1 then
        if rowBCD = target.1.2 then
          if rowLast = targetLastRowNative a b c d target.2.1 then
            if assocBasisEquiv a b (c + d) basis =
                targetBasisNative a b c d target.2.2 then 1 else 0
          else 0
        else 0
      else 0 := by
  let z : GQ4r ℝ realGauge a b c d :=
    RelTensor.mk ℝ (realGauge.D (c + d)).carrier
      (FusionColumn (realGauge.fuse c d))
      (GBR realGauge a b (c + d))
      (columnUnit c d rowCD)
      (GBR.mk realGauge a b (c + d)
        (columnUnit b (c + d) rowBCD)
        (columnBasisAssoc a b (c + d) rowLast basis))
  have hclose :
      (gq4Close ℝ realGauge a b c d).toLinearMap z =
        RelTensor.mk ℝ (realGauge.D (b + c + d)).carrier
          (GBR realGauge b c d)
          (FusionColumn (realGauge.fuse a (b + c + d)))
          (GBR.mk realGauge b c d
            (columnUnit c d rowCD)
            (columnUnit b (c + d) rowBCD))
          (fusionColumnCast ℝ realGauge a (_root_.add_assoc b c d).symm
            (columnBasisAssoc a b (c + d) rowLast basis)) := by
    unfold z
    exact gq4Close_mk ℝ realGauge a b c d
      (columnUnit c d rowCD) (columnUnit b (c + d) rowBCD)
      (columnBasisAssoc a b (c + d) rowLast basis)
  change semanticObserve a b c d target
      ((gq4Close ℝ realGauge a b c d).toLinearMap z) = _
  rw [hclose]
  rw [semanticObserve, gq4NativeCoord_mk]
  rw [LinearEquiv.symm_apply_apply]
  simp only [columnUnit]
  rw [gbrNativeColumnEquiv_fsingle]
  rw [fsingle_apply]
  by_cases hCD : rowCD = target.1.1
  · subst rowCD
    by_cases hBCD : rowBCD = target.1.2
    · subst rowBCD
      rw [if_pos rfl]
      simp only [if_true, one_smul]
      rw [columnBasisAssoc_eq]
      simp only [columnBasis, fsingle_apply]
      by_cases hLast : rowLast =
          targetLastRowNative a b c d target.2.1
      · subst rowLast
        rw [if_pos rfl]
        simp only [if_true]
        change (realRepBasis (a + (b + (c + d)))).coord
            (targetBasisNative a b c d target.2.2)
            (realRepBasis (a + (b + (c + d)))
              (assocBasisEquiv a b (c + d) basis)) = _
        rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply]
      · rw [if_neg]
        · simp only [if_neg hLast]
          exact map_zero (targetCoeffCoord a b c d target.2.2)
        · intro hframe
          apply hLast
          exact finSumFinEquiv.symm.injective hframe.symm
    · rw [if_neg]
      · simp only [if_neg hBCD]
        rw [zero_smul]
        exact map_zero (targetCoeffCoord a b c d target.2.2)
      · intro hframe
        apply hBCD
        have hp := (gbrNativeIndexEquiv ℝ realGauge b c d).injective hframe
        exact finSumFinEquiv.symm.injective (congrArg Prod.snd hp).symm
  · rw [if_neg]
    · simp only [if_neg hCD]
      rw [zero_smul]
      exact map_zero (targetCoeffCoord a b c d target.2.2)
    · intro hframe
      apply hCD
      have hp := (gbrNativeIndexEquiv ℝ realGauge b c d).injective hframe
      exact finSumFinEquiv.symm.injective (congrArg Prod.fst hp).symm

/-- The closing reassociation contributes no scalar: the unique native
generator selected by the target coordinate is observed with value one. -/
theorem semanticObserve_close_matching (a b c d : ZMod 8)
    (target : QuadTarget a b c d) :
    semanticObserve a b c d target
        ((gq4Close ℝ realGauge a b c d).toLinearMap
          (RelTensor.mk ℝ (realGauge.D (c + d)).carrier
            (FusionColumn (realGauge.fuse c d))
            (GBR realGauge a b (c + d))
            (columnUnit c d target.1.1)
            (GBR.mk realGauge a b (c + d)
              (columnUnit b (c + d) target.1.2)
              (columnBasisAssoc a b (c + d)
                (targetLastRowNative a b c d target.2.1)
                ((assocBasisEquiv a b (c + d)).symm
                  (targetBasisNative a b c d target.2.2)))))) = 1 := by
  rw [semanticObserve_close_exact]
  simp

/-! ## The two bottom connector columns -/

theorem semanticObserve_famBot (a b c d : ZMod 8)
    (source : QuadSource a b c d) (target : QuadTarget a b c d) :
    semanticObserve a b c d target
        (famBot ℝ realGauge realConnectorRealization.toConnectorFamily
          a b c d (semanticSource a b c d source)) =
      ((botCoeff a b c d source target : ℤ) : ℝ) := by
  let source4 : SourceFrame (a + b) c d :=
    (source.1.2, source.2.1)
  have h4 :
      realConnectorRealization.toConnectorFamily.T (a + b) c d
          (GBL.mk realGauge (a + b) c d
            (columnUnit (a + b) c source.1.2)
            (columnBasis (a + b + c) d source.2.1 source.2.2)) =
        ∑ middle : TargetFrame (a + b) c d,
          ∑ basis4 : Fin (realRepDim (a + b + c + d).val),
            ((connectorLinearCoeff (a + b) c d
              middle.1.val middle.2.val source.1.2.val source.2.1.val
              basis4.val source.2.2.val : ℤ) : ℝ) •
              GBR.mk realGauge (a + b) c d
                (columnUnit c d middle.1)
                (columnBasisAssoc (a + b) c d middle.2 basis4) :=
    realRawConnector_on_basis_eq_sum_assoc
    (a + b) c d source4 source.2.2
  let middle5 (middle : TargetFrame (a + b) c d)
      (basis4 : Fin (realRepDim (a + b + c + d).val)) :
      GQ5 ℝ realGauge a b c d :=
    RelTensor.mk ℝ (realGauge.D (a + b)).carrier
      (FusionColumn (realGauge.fuse a b)) (GBR realGauge (a + b) c d)
      (columnUnit a b source.1.1)
      (GBR.mk realGauge (a + b) c d
        (columnUnit c d middle.1)
        (columnBasisAssoc (a + b) c d middle.2 basis4))
  have h4lift :
      RelTensor.mk ℝ (realGauge.D (a + b)).carrier
          (FusionColumn (realGauge.fuse a b)) (GBR realGauge (a + b) c d)
          (columnUnit a b source.1.1)
          (realConnectorRealization.toConnectorFamily.T (a + b) c d
            (GBL.mk realGauge (a + b) c d
              (columnUnit (a + b) c source.1.2)
              (columnBasis (a + b + c) d source.2.1 source.2.2))) =
        ∑ middle : TargetFrame (a + b) c d,
          ∑ basis4 : Fin (realRepDim (a + b + c + d).val),
            ((connectorLinearCoeff (a + b) c d
              middle.1.val middle.2.val source.1.2.val source.2.1.val
              basis4.val source.2.2.val : ℤ) : ℝ) •
              middle5 middle basis4 := by
    rw [h4]
    simp_rw [map_sum, map_smul]
    rfl
  have hGE4 :
      GE4 ℝ realGauge a b c d (gParity ℝ realGauge (a + b) c d)
          (realConnectorRealization.toConnectorFamily.T (a + b) c d)
          (realConnectorRealization.toConnectorFamily.slotFour a b c d)
          (semanticSource a b c d source) =
        (((sgn (gParity ℝ realGauge (a + b) c d *
          FusionTable.indexParity a b source.1.1) : ℤˣ) : ℤ) : ℝ) •
          ∑ middle : TargetFrame (a + b) c d,
            ∑ basis4 : Fin (realRepDim (a + b + c + d).val),
              ((connectorLinearCoeff (a + b) c d
                middle.1.val middle.2.val source.1.2.val source.2.1.val
                basis4.val source.2.2.val : ℤ) : ℝ) •
                middle5 middle basis4 := by
    rw [semanticSource]
    rw [GE4_mk_of_mem ℝ realGauge a b c d _ _ _
      (columnUnit_mem_grading a b source.1.1)]
    rw [← Int.cast_smul_eq_zsmul ℝ]
    rw [h4lift]
    rfl
  let middle4 (middle : TargetFrame (a + b) c d)
      (out : TargetFrame a b (c + d))
      (basis5 : Fin (realRepDim (a + b + (c + d)).val)) :
      GQ4r ℝ realGauge a b c d :=
    RelTensor.mk ℝ (realGauge.D (c + d)).carrier
      (FusionColumn (realGauge.fuse c d))
      (GBR realGauge a b (c + d))
      (columnUnit c d middle.1)
      (GBR.mk realGauge a b (c + d)
        (columnUnit b (c + d) out.1)
        (columnBasisAssoc a b (c + d) out.2 basis5))
  have hGE5 (middle : TargetFrame (a + b) c d)
      (basis4 : Fin (realRepDim (a + b + c + d).val)) :
      GE5 ℝ realGauge a b c d (gParity ℝ realGauge a b (c + d))
          (realConnectorRealization.toConnectorFamily.T a b (c + d))
          (realConnectorRealization.toConnectorFamily.slotFive a b c d)
          (middle5 middle basis4) =
        (((sgn (FusionTable.indexParity c d middle.1 *
          (gParity ℝ realGauge a b (c + d) +
            FusionTable.indexParity a b source.1.1)) : ℤˣ) : ℤ) : ℝ) •
          ∑ out : TargetFrame a b (c + d),
            ∑ basis5 : Fin (realRepDim (a + b + (c + d)).val),
              ((connectorLinearCoeff a b (c + d)
                out.1.val out.2.val source.1.1.val middle.2.val
                basis5.val basis4.val : ℤ) : ℝ) •
                middle4 middle out basis5 := by
    let source5 : SourceFrame a b (c + d) :=
      (source.1.1, middle.2)
    let sourceBasis5 : Fin (realRepDim (a + b + (c + d)).val) :=
      assocBasisEquiv (a + b) c d basis4
    have h5 :
        realConnectorRealization.toConnectorFamily.T a b (c + d)
            (GBL.mk realGauge a b (c + d)
              (columnUnit a b source.1.1)
              (columnBasis (a + b) (c + d) middle.2 sourceBasis5)) =
          ∑ out : TargetFrame a b (c + d),
            ∑ basis5 : Fin (realRepDim (a + b + (c + d)).val),
              ((connectorLinearCoeff a b (c + d)
                out.1.val out.2.val source.1.1.val middle.2.val
                basis5.val sourceBasis5.val : ℤ) : ℝ) •
                GBR.mk realGauge a b (c + d)
                  (columnUnit b (c + d) out.1)
                  (columnBasisAssoc a b (c + d) out.2 basis5) := by
      change realRawConnectorFamily.T a b (c + d)
          (GBL.mk realGauge a b (c + d)
            (columnUnit a b source.1.1)
            (columnBasis (a + b) (c + d) middle.2 sourceBasis5)) = _
      exact realRawConnector_on_basis_eq_sum_assoc
        a b (c + d) source5 sourceBasis5
    have h5lift :
        RelTensor.mk ℝ (realGauge.D (c + d)).carrier
            (FusionColumn (realGauge.fuse c d))
            (GBR realGauge a b (c + d))
            (columnUnit c d middle.1)
            (realConnectorRealization.toConnectorFamily.T a b (c + d)
              (GBL.mk realGauge a b (c + d)
                (columnUnit a b source.1.1)
                (columnBasis (a + b) (c + d) middle.2 sourceBasis5))) =
          ∑ out : TargetFrame a b (c + d),
            ∑ basis5 : Fin (realRepDim (a + b + (c + d)).val),
              ((connectorLinearCoeff a b (c + d)
                out.1.val out.2.val source.1.1.val middle.2.val
                basis5.val sourceBasis5.val : ℤ) : ℝ) •
                middle4 middle out basis5 := by
      rw [h5]
      simp_rw [map_sum, map_smul]
      rfl
    unfold middle5
    rw [GE5_mk_of_mem ℝ realGauge a b c d _ _ _
      (columnUnit_mem_grading c d middle.1)
      (columnUnit_mem_grading a b source.1.1)]
    rw [← Int.cast_smul_eq_zsmul ℝ]
    rw [columnBasisAssoc_eq]
    rw [h5lift]
    rfl
  have hObserveGE5 (middle : TargetFrame (a + b) c d)
      (basis4 : Fin (realRepDim (a + b + c + d).val)) :
      semanticObserve a b c d target
          ((gq4Close ℝ realGauge a b c d).toLinearMap
            (GE5 ℝ realGauge a b c d
              (gParity ℝ realGauge a b (c + d))
              (realConnectorRealization.toConnectorFamily.T a b (c + d))
              (realConnectorRealization.toConnectorFamily.slotFive a b c d)
              (middle5 middle basis4))) =
        if middle.1 = target.1.1 then
          ((((sgn (FusionTable.indexParity c d middle.1 *
            (gParity ℝ realGauge a b (c + d) +
              FusionTable.indexParity a b source.1.1)) : ℤˣ) : ℤ) : ℝ)) *
            ((connectorLinearCoeff a b (c + d)
              target.1.2.val target.2.1.val source.1.1.val middle.2.val
              target.2.2.val basis4.val : ℤ) : ℝ)
        else 0 := by
    rw [hGE5]
    rw [map_smul, map_smul]
    simp_rw [map_sum, map_smul]
    rw [Fintype.sum_prod_type]
    by_cases hCD : middle.1 = target.1.1
    · rw [if_pos hCD]
      rw [Finset.sum_eq_single target.1.2]
      · rw [Finset.sum_eq_single
          (targetLastRowNative a b c d target.2.1)]
        · rw [Finset.sum_eq_single
            ((assocBasisEquiv a b (c + d)).symm
              (targetBasisNative a b c d target.2.2))]
          · simp only [middle4, semanticObserve_close_exact,
              hCD, if_true, Equiv.apply_symm_apply, smul_eq_mul,
              mul_one]
            rfl
          · intro other _ hne
            simp only [middle4, semanticObserve_close_exact,
              hCD, if_true, Equiv.apply_eq_iff_eq_symm_apply,
              if_neg hne, smul_zero]
          · exact fun h => absurd
              (Finset.mem_univ
                ((assocBasisEquiv a b (c + d)).symm
                  (targetBasisNative a b c d target.2.2))) h
        · intro other _ hne
          apply Finset.sum_eq_zero
          intro basis5 _
          simp only [middle4, semanticObserve_close_exact,
            hCD, if_true, if_neg hne, smul_zero]
        · exact fun h => absurd
            (Finset.mem_univ
              (targetLastRowNative a b c d target.2.1)) h
      · intro other _ hne
        apply Finset.sum_eq_zero
        intro rowLast _
        apply Finset.sum_eq_zero
        intro basis5 _
        simp only [middle4, semanticObserve_close_exact,
          hCD, if_true, if_neg hne, smul_zero]
      · exact fun h => absurd (Finset.mem_univ target.1.2) h
    · rw [if_neg hCD]
      have hsum :
          (∑ rowBCD : FusionTable.Index b (c + d),
            ∑ rowLast : FusionTable.Index a (b + (c + d)),
              ∑ basis5 : Fin (realRepDim (a + b + (c + d)).val),
                ((connectorLinearCoeff a b (c + d)
                  rowBCD.val rowLast.val source.1.1.val middle.2.val
                  basis5.val basis4.val : ℤ) : ℝ) •
                  semanticObserve a b c d target
                    ((gq4Close ℝ realGauge a b c d).toLinearMap
                      (middle4 middle (rowBCD, rowLast) basis5))) = 0 := by
        apply Finset.sum_eq_zero
        intro rowBCD _
        apply Finset.sum_eq_zero
        intro rowLast _
        apply Finset.sum_eq_zero
        intro basis5 _
        simp only [middle4, semanticObserve_close_exact,
          if_neg hCD, smul_zero]
      rw [hsum, smul_zero]
  change semanticObserve a b c d target
      ((gq4Close ℝ realGauge a b c d).toLinearMap
        (GE5 ℝ realGauge a b c d (gParity ℝ realGauge a b (c + d))
          (realConnectorRealization.toConnectorFamily.T a b (c + d))
          (realConnectorRealization.toConnectorFamily.slotFive a b c d)
          (GE4 ℝ realGauge a b c d (gParity ℝ realGauge (a + b) c d)
            (realConnectorRealization.toConnectorFamily.T (a + b) c d)
            (realConnectorRealization.toConnectorFamily.slotFour a b c d)
            (semanticSource a b c d source)))) = _
  rw [hGE4]
  rw [map_smul, map_smul, map_smul]
  simp_rw [map_sum, map_smul]
  simp_rw [hObserveGE5]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single target.1.1]
  · simp only [if_true, smul_eq_mul]
    unfold botCoeff
    simp_rw [sumRange_eq_sumFin]
    have hsign :
        ((((sgn (gParity ℝ realGauge (a + b) c d *
          FusionTable.indexParity a b source.1.1) : ℤˣ) : ℤ) : ℝ)) *
          ((((sgn (FusionTable.indexParity c d target.1.1 *
            (gParity ℝ realGauge a b (c + d) +
              FusionTable.indexParity a b source.1.1)) : ℤˣ) : ℤ) : ℝ)) =
        ((koszulSign
              (connectorParityNat (a + b) c d *
                rowParityNat a b source.1.1.val) *
            koszulSign
              (rowParityNat c d target.1.1.val *
                (connectorParityNat a b (c + d) +
                  rowParityNat a b source.1.1.val)) : ℤ) : ℝ) := by
      rw [semanticBottomSign_eq_koszulSigns]
      rw [← congrArg ZMod.val (rawParity_eq_gParity (a + b) c d)]
      rw [← rowParityNat_eq_indexParity_val a b source.1.1]
      rw [← rowParityNat_eq_indexParity_val c d target.1.1]
      rw [← congrArg ZMod.val (rawParity_eq_gParity a b (c + d))]
      rfl
    have hguard :
        (∑ rowABCD : Fin (fusionRank (a + b) (c + d)),
          ∑ basis4 : Fin (coefficientRank (a + b + c + d)),
            if connectorLinearCoeff (a + b) c d
                target.1.1.val rowABCD.val source.1.2.val source.2.1.val
                basis4.val source.2.2.val = 0 then 0
            else
              connectorLinearCoeff (a + b) c d
                  target.1.1.val rowABCD.val source.1.2.val source.2.1.val
                  basis4.val source.2.2.val *
                connectorLinearCoeff a b (c + d)
                  target.1.2.val target.2.1.val source.1.1.val rowABCD.val
                  target.2.2.val basis4.val) =
        ∑ rowABCD : Fin (fusionRank (a + b) (c + d)),
          ∑ basis4 : Fin (coefficientRank (a + b + c + d)),
            connectorLinearCoeff (a + b) c d
                target.1.1.val rowABCD.val source.1.2.val source.2.1.val
                basis4.val source.2.2.val *
              connectorLinearCoeff a b (c + d)
                target.1.2.val target.2.1.val source.1.1.val rowABCD.val
                target.2.2.val basis4.val := by
      apply Finset.sum_congr rfl
      intro rowABCD _
      apply Finset.sum_congr rfl
      intro basis4 _
      by_cases h : connectorLinearCoeff (a + b) c d
          target.1.1.val rowABCD.val source.1.2.val source.2.1.val
          basis4.val source.2.2.val = 0 <;> simp [h]
    rw [hguard]
    push_cast
    have hfactor :
        (∑ rowABCD : FusionTable.Index (a + b) (c + d),
          ∑ basis4 : Fin (realRepDim (a + b + c + d).val),
            ((connectorLinearCoeff (a + b) c d
              target.1.1.val rowABCD.val source.1.2.val source.2.1.val
              basis4.val source.2.2.val : ℤ) : ℝ) *
              (((((sgn (FusionTable.indexParity c d target.1.1 *
                (gParity ℝ realGauge a b (c + d) +
                  FusionTable.indexParity a b source.1.1)) : ℤˣ) : ℤ) : ℝ)) *
                ((connectorLinearCoeff a b (c + d)
                  target.1.2.val target.2.1.val source.1.1.val rowABCD.val
                  target.2.2.val basis4.val : ℤ) : ℝ))) =
          ((((sgn (FusionTable.indexParity c d target.1.1 *
            (gParity ℝ realGauge a b (c + d) +
              FusionTable.indexParity a b source.1.1)) : ℤˣ) : ℤ) : ℝ)) *
            ∑ rowABCD : FusionTable.Index (a + b) (c + d),
              ∑ basis4 : Fin (realRepDim (a + b + c + d).val),
                ((connectorLinearCoeff (a + b) c d
                  target.1.1.val rowABCD.val source.1.2.val source.2.1.val
                  basis4.val source.2.2.val : ℤ) : ℝ) *
                  ((connectorLinearCoeff a b (c + d)
                    target.1.2.val target.2.1.val source.1.1.val rowABCD.val
                    target.2.2.val basis4.val : ℤ) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rowABCD _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro basis4 _
      ring
    rw [hfactor]
    rw [← mul_assoc, hsign]
    push_cast
    rfl
  · intro other _ hne
    apply Finset.sum_eq_zero
    intro rowABCD _
    apply Finset.sum_eq_zero
    intro basis4 _
    simp only [if_neg hne, smul_zero]
  · exact fun h => absurd (Finset.mem_univ target.1.1) h

end RealPChiRouteBottom
end Superfusion.RMod.RawDCT
