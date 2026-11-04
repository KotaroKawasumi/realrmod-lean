import Superfusion.GaugeChi.QuadChaseNativeExpansion
import Superfusion.RMod.RawDCT.RealConnectorRealization
import Superfusion.RMod.RawDCT.RealPChiKernel

/-!
# Semantic route coordinates for the exact real pentagon kernel

This file connects the finite indices of `RealPChiKernel` to the existing
semantic fourfold source and target.  It contains no new table and performs
no finite decision: all numerical coefficients continue to come from the
raw fusion and connector data.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiRouteBridge

open GaugeChi
open Bimod
open RModCoordinate
open RealPChiKernel
open scoped TensorProduct

/-! ## Binary coordinate columns -/

/-- The canonical real basis vector, with its carrier explicitly ascribed to
the concrete gauge.  This avoids choosing a second definitionally equal
module instance while elaborating slot actions. -/
private noncomputable abbrev gaugeBasis (a : ZMod 8)
    (basis : Fin (realRepDim a.val)) : (realGauge.D a).carrier :=
  realRepBasis a basis

/-- Scalar evaluation on a fusion column, with the column type kept
explicit so that the concrete real instance is not re-elaborated. -/
private theorem fusionColumn_smul_apply
    {P B : SuperAlgebra ℝ} {p q : ℕ}
    (phi : SuperAlgEquiv P (B.matrixSuper p q)) (r : ℝ)
    (v : FusionColumn phi) (i : Fin p ⊕ Fin q) :
    ((r • v : FusionColumn phi) i) = r • v i :=
  rfl

/-- The raw representative and gauge-ascribed scalar actions agree on a
canonical basis vector. -/
private theorem rawBasis_smul_eq_gaugeBasis_smul (a : ZMod 8)
    (basis : Fin (realRepDim a.val)) (r : ℝ) :
    (show (realGauge.D a).carrier from r • realRepBasis a basis) =
      r • gaugeBasis a basis := by
  rfl

/-- A semantic fusion-column basis vector at one raw row and one canonical
coefficient-basis coordinate. -/
noncomputable def columnBasis (a b : ZMod 8)
    (row : FusionTable.Index a b)
    (basis : Fin (realRepDim (a + b).val)) :
  FusionColumn (realGauge.fuse a b) :=
  fsingle (realGauge.fuse a b) (FusionTable.frameIndex a b row)
    (gaugeBasis (a + b) basis)

/-- The unit fusion-column at one raw row. -/
noncomputable def columnUnit (a b : ZMod 8)
    (row : FusionTable.Index a b) : FusionColumn (realGauge.fuse a b) :=
  fsingle (realGauge.fuse a b) (FusionTable.frameIndex a b row) 1

@[simp]
theorem columnBasis_apply_same (a b : ZMod 8)
    (row : FusionTable.Index a b)
    (basis : Fin (realRepDim (a + b).val)) :
    columnBasis a b row basis (FusionTable.frameIndex a b row) =
      gaugeBasis (a + b) basis := by
  rw [columnBasis, fsingle_apply, if_pos rfl]

theorem columnBasis_apply_ne (a b : ZMod 8)
    (row target : FusionTable.Index a b)
    (basis : Fin (realRepDim (a + b).val)) (h : row ≠ target) :
    columnBasis a b row basis (FusionTable.frameIndex a b target) = 0 := by
  rw [columnBasis, fsingle_apply, if_neg]
  intro hframe
  exact h (finSumFinEquiv.symm.injective hframe).symm

/-- The zeroth coefficient basis vector is the algebra unit, hence the two
singleton-column spellings used by the source generator coincide. -/
theorem columnBasis_unit_eq_columnUnit (a b : ZMod 8)
    (row : FusionTable.Index a b) :
    columnBasis a b row (coefficientUnitIndex (a + b)) =
      columnUnit a b row := by
  unfold columnBasis columnUnit gaugeBasis
  rw [GaugeChi.realRepBasis_zero (a + b)
    (coefficientUnitIndex (a + b)) rfl]
  rfl

/-! ## Row parity and homogeneous unit columns -/

/-- The natural-bit row parity used by the executable kernel is the raw
fusion table's `ZMod 2` row degree. -/
theorem rowParityNat_cast_indexParity (a b : ZMod 8)
    (row : FusionTable.Index a b) :
    (rowParityNat a b row.val : ZMod 2) =
      FusionTable.indexParity a b row := by
  unfold rowParityNat FusionTable.indexParity
  by_cases h : row.val < (realSize a b).1 <;> simp [h]

/-- The raw even-first row degree agrees with the semantic sum-frame
degree. -/
theorem indexParity_eq_sumParity (a b : ZMod 8)
    (row : FusionTable.Index a b) :
    FusionTable.indexParity a b row =
      sumParity (realSize a b).1 (realSize a b).2
        (FusionTable.frameIndex a b row) := by
  have hback : finSumFinEquiv (FusionTable.frameIndex a b row) = row := by
    exact finSumFinEquiv.apply_symm_apply row
  rcases h : FusionTable.frameIndex a b row with u | u
  · have hval : row.val = u.val := by
      rw [← hback, h]
      rfl
    unfold FusionTable.indexParity sumParity
    rw [if_pos (hval.trans_lt u.isLt)]
    rfl
  · have hval : row.val = (realSize a b).1 + u.val := by
      rw [← hback, h]
      rfl
    unfold FusionTable.indexParity sumParity
    rw [if_neg]
    · rfl
    · rw [hval]
      omega

/-- A unit singleton column is homogeneous in exactly its row parity. -/
theorem columnUnit_mem_grading (a b : ZMod 8)
    (row : FusionTable.Index a b) :
    columnUnit a b row ∈ FusionColumn.grading (realGauge.fuse a b)
      (FusionTable.indexParity a b row) := by
  unfold columnUnit
  apply GaugeChi.fsingle_mem_grading
  simp only [realGauge_size]
  rw [← indexParity_eq_sumParity, Coeff.add_self_eq_zero]
  exact SetLike.one_mem_graded (realGauge.D (a + b)).grading

/-! ## Semantic and executable sign conventions -/

/-- The natural representative of raw row parity is unchanged by viewing
the same bit in `ZMod 2`. -/
theorem rowParityNat_eq_indexParity_val (a b : ZMod 8)
    (row : FusionTable.Index a b) :
    rowParityNat a b row.val = (FusionTable.indexParity a b row).val := by
  unfold rowParityNat FusionTable.indexParity
  by_cases h : row.val < (realSize a b).1
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]
    rfl

/-- The semantic connector family's forced parity is the raw table parity. -/
theorem rawParity_eq_gParity (a b c : ZMod 8) :
    realTData.parity a b c = gParity ℝ realGauge a b c :=
  realRawConnectorFamily.parity_eq a b c

/-- A semantic Koszul unit has the same real scalar as the executable
integer sign convention. -/
theorem semanticSign_eq_koszulSign (p q : ZMod 2) :
    ((((sgn (p * q) : ℤˣ) : ℤ) : ℝ)) =
      ((koszulSign (p.val * q.val) : ℤ) : ℝ) := by
  rcases zmod2_cases p with hp | hp <;> subst p
  all_goals rcases zmod2_cases q with hq | hq <;> subst q
  all_goals norm_num [koszulSign, Superfusion.sgn] <;> decide

/-- The canonical coefficient realization, ascribed to the concrete gauge
carrier so that all algebra operations use the same `Field ℝ` instance. -/
private noncomputable def semanticCoeff (a : ZMod 8) (x : Coeff a) :
    (realGauge.D a).carrier :=
  Coeff.semantic a x

@[simp]
theorem semantic_coefficientBasis (a : ZMod 8)
    (basis : Fin (realRepDim a.val)) :
    semanticCoeff a (coefficientBasis a basis) = realRepBasis a basis := by
  change (realRepBasis a).equivFun.symm (coefficientBasis a basis) =
    realRepBasis a basis
  rw [Module.Basis.equivFun_symm_apply]
  simp [coefficientBasis]

/-- The same basis realization in the original representative carrier.
This spelling is used with `semanticFusionEntry`, whose definition predates
the concrete gauge bundle. -/
@[simp]
theorem rawSemantic_coefficientBasis (a : ZMod 8)
    (basis : Fin (realRepDim a.val)) :
    Coeff.semantic a (coefficientBasis a basis) =
      realRepBasis a basis := by
  change (realRepBasis a).equivFun.symm (coefficientBasis a basis) =
    realRepBasis a basis
  rw [Module.Basis.equivFun_symm_apply]
  simp [coefficientBasis]

private theorem semanticCoeff_mul (a : ZMod 8) (x y : Coeff a) :
    semanticCoeff a (Coeff.mul a x y) =
      semanticCoeff a x * semanticCoeff a y := by
  change Coeff.semantic a (Coeff.mul a x y) =
    Coeff.semantic a x * Coeff.semantic a y
  exact Coeff.semantic_mul a x y

theorem semanticCoeff_eq_sum (a : ZMod 8) (x : Coeff a) :
    semanticCoeff a x =
      ∑ g : Fin (realRepDim a.val), x g • realRepBasis a g := by
  change (realRepBasis a).equivFun.symm x = _
  exact Module.Basis.equivFun_symm_apply (realRepBasis a) x

/-- Coordinate expansion in the original representative carrier. -/
theorem rawSemantic_eq_sum (a : ZMod 8) (x : Coeff a) :
    Coeff.semantic a x =
      ∑ g : Fin (realRepDim a.val), x g • realRepBasis a g := by
  change (realRepBasis a).equivFun.symm x = _
  exact Module.Basis.equivFun_symm_apply (realRepBasis a) x

theorem coefficientBasis_unit (a : ZMod 8) :
    coefficientBasis a (coefficientUnitIndex a) = Coeff.one a := by
  funext g
  simp only [coefficientBasis, coefficientUnitIndex, Coeff.one]
  by_cases hg : g.val = 0
  · rw [if_pos hg, if_pos]
    exact Fin.ext hg
  · rw [if_neg hg, if_neg]
    intro h
    exact hg (congrArg Fin.val h)

/-- Associativity transport on canonical coefficient-basis indices. -/
def assocBasisEquiv (a b c : ZMod 8) :
    Fin (realRepDim (a + b + c).val) ≃
      Fin (realRepDim (a + (b + c)).val) :=
  finCongr (congrArg (fun x : ZMod 8 => realRepDim x.val)
    (_root_.add_assoc a b c))

/-! ## Equality transports for binary columns -/

/-- Transport a binary fusion row when the first label is changed by an
equality. -/
def fusionRowCastFst (d : ZMod 8) {x y : ZMod 8} (h : x = y)
    (row : FusionTable.Index x d) : FusionTable.Index y d :=
  Fin.cast (congrArg (fun z : ZMod 8 => fusionRank z d) h) row

/-- Transport an endpoint coefficient coordinate under the same change of
the first fusion label. -/
def fusionBasisCastFst (d : ZMod 8) {x y : ZMod 8} (h : x = y)
    (basis : Fin (realRepDim (x + d).val)) :
    Fin (realRepDim (y + d).val) :=
  Fin.cast (congrArg (fun z : ZMod 8 => realRepDim (z + d).val) h) basis

@[simp]
theorem fusionRowCastFst_val (d : ZMod 8) {x y : ZMod 8} (h : x = y)
    (row : FusionTable.Index x d) :
    (fusionRowCastFst d h row).val = row.val :=
  rfl

@[simp]
theorem fusionBasisCastFst_val (d : ZMod 8) {x y : ZMod 8} (h : x = y)
    (basis : Fin (realRepDim (x + d).val)) :
    (fusionBasisCastFst d h basis).val = basis.val :=
  rfl

theorem gColumnCastFst_columnBasis (d : ZMod 8) {x y : ZMod 8}
    (h : x = y) (row : FusionTable.Index x d)
    (basis : Fin (realRepDim (x + d).val)) :
    gColumnCastFst ℝ realGauge d h (columnBasis x d row basis) =
      columnBasis y d (fusionRowCastFst d h row)
        (fusionBasisCastFst d h basis) := by
  subst y
  rfl

theorem gColumnCastFst_columnUnit (d : ZMod 8) {x y : ZMod 8}
    (h : x = y) (row : FusionTable.Index x d) :
    gColumnCastFst ℝ realGauge d h (columnUnit x d row) =
      columnUnit y d (fusionRowCastFst d h row) := by
  subst y
  rfl

/-- A right-route output basis column indexed in the connector's original
left-associated coefficient basis. -/
noncomputable def columnBasisAssoc (a b c : ZMod 8)
    (row : FusionTable.Index a (b + c))
    (basis : Fin (realRepDim (a + b + c).val)) :
    FusionColumn (realGauge.fuse a (b + c)) :=
  fsingle (realGauge.fuse a (b + c))
    (FusionTable.frameIndex a (b + c) row)
    ((realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
      (realRepBasis (a + b + c) basis))

theorem columnBasisAssoc_eq (a b c : ZMod 8)
    (row : FusionTable.Index a (b + c))
    (basis : Fin (realRepDim (a + b + c).val)) :
    columnBasisAssoc a b c row basis =
      columnBasis a (b + c) row (assocBasisEquiv a b c basis) := by
  unfold columnBasisAssoc columnBasis
  rw [RModCoordinate.RawSemanticSkeletalData.gaugeCast_realRepBasis]
  rfl

/-- Equality transport of a coefficient vector. -/
private def coeffCast {u v : ZMod 8} (h : u = v) : Coeff u → Coeff v :=
  cast (congrArg Coeff h)

private theorem coeffCast_apply {u v : ZMod 8} (h : u = v)
    (x : Coeff u) (g : Fin (realRepDim v.val)) :
    coeffCast h x g =
      x ((finCongr (congrArg
        (fun z : ZMod 8 => realRepDim z.val) h)).symm g) := by
  subst v
  rfl

private theorem semanticCoeff_cast {u v : ZMod 8} (h : u = v)
    (x : Coeff u) :
    semanticCoeff v (coeffCast h x) =
      (realGauge.gaugeCast h).toAlgEquiv (semanticCoeff u x) := by
  subst v
  rfl

/-! ## Native ternary frame indices -/

/-- Coordinate/source-frame identification with the semantic left frame. -/
noncomputable def leftFrameEquiv (a b c : ZMod 8) :
    SourceFrame a b c ≃
      (Fin (realGauge.gaugeSizeL a b c).1 ⊕
        Fin (realGauge.gaugeSizeL a b c).2) :=
  ((finSumFinEquiv.symm.prodCongr finSumFinEquiv.symm).trans
    (gblIndexEquiv ℝ realGauge a b c))

/-- Coordinate/target-frame identification with the semantic native right
frame. -/
noncomputable def rightFrameEquiv (a b c : ZMod 8) :
    TargetFrame a b c ≃
      (Fin (realGauge.gaugeSizeR a b c).1 ⊕
        Fin (realGauge.gaugeSizeR a b c).2) :=
  ((finSumFinEquiv.symm.prodCongr finSumFinEquiv.symm).trans
    (gbrNativeIndexEquiv ℝ realGauge a b c))

/-- A raw source-frame pair in the semantic left dictionary. -/
noncomputable def leftFrameIndex (a b c : ZMod 8)
    (source : SourceFrame a b c) :
    Fin (realGauge.gaugeSizeL a b c).1 ⊕
      Fin (realGauge.gaugeSizeL a b c).2 :=
  gblIndexEquiv ℝ realGauge a b c
    (FusionTable.frameIndex a b source.1,
      FusionTable.frameIndex (a + b) c source.2)

@[simp]
theorem leftFrameIndex_eq_equiv (a b c : ZMod 8)
    (source : SourceFrame a b c) :
    leftFrameIndex a b c source = leftFrameEquiv a b c source :=
  rfl

/-- A raw target-frame pair in the semantic native right dictionary. -/
noncomputable def rightFrameIndex (a b c : ZMod 8)
    (target : TargetFrame a b c) :
    Fin (realGauge.gaugeSizeR a b c).1 ⊕
      Fin (realGauge.gaugeSizeR a b c).2 :=
  gbrNativeIndexEquiv ℝ realGauge a b c
    (FusionTable.frameIndex b c target.1,
      FusionTable.frameIndex a (b + c) target.2)

@[simp]
theorem rightFrameIndex_eq_equiv (a b c : ZMod 8)
    (target : TargetFrame a b c) :
    rightFrameIndex a b c target = rightFrameEquiv a b c target :=
  rfl

/-- Unfolding form of `rightFrameIndex`, useful when a native dictionary
theorem has exposed the underlying product index. -/
@[simp]
theorem rightFrameIndex_eq_native (a b c : ZMod 8)
    (target : TargetFrame a b c) :
    rightFrameIndex a b c target =
      gbrNativeIndexEquiv ℝ realGauge a b c
        (FusionTable.frameIndex b c target.1,
          FusionTable.frameIndex a (b + c) target.2) :=
  rfl

private theorem sumPos_frameEquiv {p q sigma : ℕ}
    (h : p + q = sigma) (u : Fin p ⊕ Fin q) :
    sumPos u = (Superfusion.frameEquiv h u).val := by
  rcases u with u | u <;> rfl

theorem leftFrameIndex_sumPos (a b c : ZMod 8)
    (source : SourceFrame a b c) :
    sumPos (leftFrameIndex a b c source) =
      sourceFramePosition a b c source.1.val source.2.val := by
  calc
    sumPos (leftFrameIndex a b c source) =
        (RModCoordinate.RawSemanticConnector.leftFrameEquiv a b c
          (leftFrameIndex a b c source)).val :=
      sumPos_frameEquiv
        (RModCoordinate.RawSemanticConnector.leftTotal_eq_sigma a b c) _
    _ = sourceFramePosition a b c source.1.val source.2.val := by
      exact (sourceFramePosition_eq_realTLeftPosition
        a b c source.1 source.2).symm

theorem rightFrameIndex_sumPos (a b c : ZMod 8)
    (target : TargetFrame a b c) :
    sumPos (rightFrameIndex a b c target) =
      targetFramePosition a b c target.1.val target.2.val := by
  calc
    sumPos (rightFrameIndex a b c target) =
        (RModCoordinate.RawSemanticConnector.rightFrameEquiv a b c
          (rightFrameIndex a b c target)).val :=
      sumPos_frameEquiv
        (RModCoordinate.RawSemanticConnector.rightTotal_eq_sigma a b c) _
    _ = targetFramePosition a b c target.1.val target.2.val := by
      exact (targetFramePosition_eq_realTRightPosition
        a b c target.1 target.2).symm

/-! ## One exact connector column -/

/-- The semantic realization of a raw coefficient vector after the ternary
associativity cast, expanded in the transported canonical basis. -/
theorem gaugeCast_semantic (a b c : ZMod 8) (x : Coeff (a + b + c)) :
    (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
        (semanticCoeff (a + b + c) x) =
      ∑ g : Fin (realRepDim (a + (b + c)).val),
        x ((assocBasisEquiv a b c).symm g) •
          realRepBasis (a + (b + c)) g := by
  rw [← semanticCoeff_cast (_root_.add_assoc a b c) x]
  change Coeff.semantic (a + (b + c))
      (coeffCast (_root_.add_assoc a b c) x) = _
  simp only [Coeff.semantic, Module.Basis.equivFun_symm_apply,
    coeffCast_apply, assocBasisEquiv]

/-- A native semantic connector entry is the associativity transport of the
matching stored raw coefficient-algebra entry. -/
theorem forwardMatrix_entry_semantic (a b c : ZMod 8)
    (target : TargetFrame a b c) (source : SourceFrame a b c) :
    RModCoordinate.RawSemanticConnector.forwardMatrix a b c
        (rightFrameIndex a b c target) (leftFrameIndex a b c source) =
      (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
        (semanticCoeff (a + b + c)
          (realTForwardEntry a b c target.1 target.2 source.1 source.2)) := by
  rw [RModCoordinate.RawSemanticSkeletalData.forwardMatrix_eq_native_raw,
    matOfCoeff₂_apply, gaugeCast_semantic]
  apply Finset.sum_congr rfl
  intro g _
  rw [leftFrameIndex_sumPos, rightFrameIndex_sumPos]
  simp only [realTForwardEntry, assocBasisEquiv]
  rw [sourceFramePosition_eq_realTLeftPosition,
    targetFramePosition_eq_realTRightPosition]
  rfl

/-- Multiplying one frozen connector entry by a canonical source basis
vector gives exactly the integer column used by `connectorLinearCoeff`. -/
theorem forwardMatrix_mul_basis (a b c : ZMod 8)
    (target : TargetFrame a b c) (source : SourceFrame a b c)
    (sourceBasis : Fin (realRepDim (a + b + c).val)) :
    RModCoordinate.RawSemanticConnector.forwardMatrix a b c
        (rightFrameIndex a b c target) (leftFrameIndex a b c source) *
        (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
          (realRepBasis (a + b + c) sourceBasis) =
      ∑ targetBasis : Fin (realRepDim (a + (b + c)).val),
        ((connectorLinearCoeff a b c target.1.val target.2.val
          source.1.val source.2.val targetBasis.val sourceBasis.val : ℤ) : ℝ) •
          realRepBasis (a + (b + c)) targetBasis := by
  rw [forwardMatrix_entry_semantic]
  rw [← semantic_coefficientBasis]
  rw [← map_mul,
    ← semanticCoeff_mul,
    gaugeCast_semantic]
  apply Finset.sum_congr rfl
  intro targetBasis _
  congr 1
  symm
  have hval : ((assocBasisEquiv a b c).symm targetBasis).val =
      targetBasis.val := rfl
  rw [← hval]
  exact connectorLinearCoeff_cast a b c target source
    ((assocBasisEquiv a b c).symm targetBasis) sourceBasis

/-- The explicit dense native column obtained from one left-frame basis
generator. -/
noncomputable def connectorColumn (a b c : ZMod 8)
    (source : SourceFrame a b c)
    (sourceBasis : Fin (realRepDim (a + b + c).val)) :
    FusionColumn (realGauge.gaugeRouteR a b c) :=
  fun y =>
    let target := (rightFrameEquiv a b c).symm y
    ∑ targetBasis : Fin (realRepDim (a + (b + c)).val),
      ((connectorLinearCoeff a b c target.1.val target.2.val
        source.1.val source.2.val targetBasis.val sourceBasis.val : ℤ) : ℝ) •
        gaugeBasis (a + (b + c)) targetBasis

/-- The semantic right-route element whose native dictionary column is the
exact dense kernel column. -/
noncomputable def connectorImage (a b c : ZMod 8)
    (source : SourceFrame a b c)
    (sourceBasis : Fin (realRepDim (a + b + c).val)) :
    GBR realGauge a b c :=
  (gbrNativeColumnEquiv ℝ realGauge a b c).symm
    (connectorColumn a b c source sourceBasis)

@[simp]
theorem connectorImage_toColumn (a b c : ZMod 8)
    (source : SourceFrame a b c)
    (sourceBasis : Fin (realRepDim (a + b + c).val)) :
    gbrNativeColumnEquiv ℝ realGauge a b c
        (connectorImage a b c source sourceBasis) =
      connectorColumn a b c source sourceBasis :=
  (gbrNativeColumnEquiv ℝ realGauge a b c).apply_symm_apply _

/-- The actual semantic connector sends a singleton source basis generator
to the dense integer column `connectorImage`. -/
theorem realRawConnector_on_basis (a b c : ZMod 8)
    (source : SourceFrame a b c)
    (sourceBasis : Fin (coefficientRank (a + b + c))) :
    realRawConnectorFamily.T a b c
        (GBL.mk realGauge a b c
          (columnUnit a b source.1)
          (columnBasis (a + b) c source.2 sourceBasis)) =
      connectorImage a b c source sourceBasis := by
  change gtOfTNative ℝ realGauge a b c
      (RModCoordinate.RawSemanticConnector.forwardMatrix a b c)
      (GBL.mk realGauge a b c
        (fsingle (realGauge.fuse a b)
          (FusionTable.frameIndex a b source.1) 1)
        (fsingle (realGauge.fuse (a + b) c)
          (FusionTable.frameIndex (a + b) c source.2)
          (realRepBasis (a + b + c) sourceBasis))) = _
  apply gtOfTNative_fsingle ℝ realGauge a b c
  intro y
  rw [connectorImage_toColumn]
  let target : TargetFrame a b c := (rightFrameEquiv a b c).symm y
  have hy : rightFrameIndex a b c target = y := by
    rw [rightFrameIndex_eq_equiv]
    exact (rightFrameEquiv a b c).apply_symm_apply y
  unfold connectorColumn
  rw [show (rightFrameEquiv a b c).symm y = target from rfl]
  rw [← hy]
  exact forwardMatrix_mul_basis a b c target source sourceBasis

/-- Expansion of the exact connector image into semantic native-frame basis
generators. -/
theorem connectorImage_eq_sum (a b c : ZMod 8)
    (source : SourceFrame a b c)
    (sourceBasis : Fin (realRepDim (a + b + c).val)) :
    connectorImage a b c source sourceBasis =
      ∑ target : TargetFrame a b c,
        ∑ targetBasis : Fin (realRepDim (a + (b + c)).val),
          ((connectorLinearCoeff a b c target.1.val target.2.val
            source.1.val source.2.val targetBasis.val sourceBasis.val : ℤ) : ℝ) •
            GBR.mk realGauge a b c
              (columnUnit b c target.1)
              (columnBasis a (b + c) target.2 targetBasis) := by
  apply (gbrNativeColumnEquiv ℝ realGauge a b c).injective
  rw [connectorImage_toColumn, map_sum]
  simp_rw [map_sum, map_smul, columnUnit, columnBasis,
    gbrNativeColumnEquiv_fsingle]
  simp_rw [← rightFrameIndex_eq_native]
  funext y
  let basisTerm (target' : TargetFrame a b c)
      (targetBasis : Fin (realRepDim (a + (b + c)).val)) :
      FusionColumn (realGauge.gaugeRouteR a b c) :=
    ((connectorLinearCoeff a b c target'.1.val target'.2.val
      source.1.val source.2.val targetBasis.val sourceBasis.val : ℤ) : ℝ) •
      fsingle (realGauge.gaugeRouteR a b c)
        (rightFrameIndex a b c target')
        (gaugeBasis (a + (b + c)) targetBasis)
  let rhsTerm : TargetFrame a b c →
      FusionColumn (realGauge.gaugeRouteR a b c) := fun target' =>
    ∑ targetBasis, basisTerm target' targetBasis
  change connectorColumn a b c source sourceBasis y =
    (∑ target', rhsTerm target') y
  have houter :
      ((∑ target', rhsTerm target') :
        FusionColumn (realGauge.gaugeRouteR a b c)) y =
        ∑ target', rhsTerm target' y :=
    Finset.sum_apply y Finset.univ rhsTerm
  rw [houter]
  have hinner (target' : TargetFrame a b c) :
      rhsTerm target' y = ∑ targetBasis, basisTerm target' targetBasis y := by
    unfold rhsTerm
    exact Finset.sum_apply y Finset.univ (basisTerm target')
  let target : TargetFrame a b c := (rightFrameEquiv a b c).symm y
  have hy : rightFrameIndex a b c target = y := by
    rw [rightFrameIndex_eq_equiv]
    exact (rightFrameEquiv a b c).apply_symm_apply y
  rw [connectorColumn]
  rw [show (rightFrameEquiv a b c).symm y = target from rfl]
  rw [Finset.sum_eq_single target]
  · rw [hinner]
    apply Finset.sum_congr rfl
    intro targetBasis _
    unfold basisTerm
    rw [fusionColumn_smul_apply, fsingle_apply, hy, if_pos]
    rfl
  · intro other _ hne
    have hframe : rightFrameIndex a b c other ≠ y := by
      intro h
      apply hne
      apply (rightFrameEquiv a b c).injective
      simpa only [rightFrameIndex_eq_equiv] using h.trans hy.symm
    rw [hinner]
    apply Finset.sum_eq_zero
    intro targetBasis _
    unfold basisTerm
    rw [fusionColumn_smul_apply, fsingle_apply,
      if_neg (fun h => hframe h.symm), smul_zero]
  · exact fun h => absurd (Finset.mem_univ target) h

/-- The actual semantic connector has the same dense native basis
expansion. -/
theorem realRawConnector_on_basis_eq_sum (a b c : ZMod 8)
    (source : SourceFrame a b c)
    (sourceBasis : Fin (realRepDim (a + b + c).val)) :
    realRawConnectorFamily.T a b c
        (GBL.mk realGauge a b c
          (columnUnit a b source.1)
          (columnBasis (a + b) c source.2 sourceBasis)) =
      ∑ target : TargetFrame a b c,
        ∑ targetBasis : Fin (realRepDim (a + (b + c)).val),
          ((connectorLinearCoeff a b c target.1.val target.2.val
            source.1.val source.2.val targetBasis.val sourceBasis.val : ℤ) : ℝ) •
            GBR.mk realGauge a b c
              (columnUnit b c target.1)
              (columnBasis a (b + c) target.2 targetBasis) := by
  rw [realRawConnector_on_basis, connectorImage_eq_sum]

/-- The same connector expansion, indexed in the original left-associated
coefficient basis.  The output column performs the semantic associativity
cast explicitly. -/
theorem realRawConnector_on_basis_eq_sum_assoc (a b c : ZMod 8)
    (source : SourceFrame a b c)
    (sourceBasis : Fin (realRepDim (a + b + c).val)) :
    realRawConnectorFamily.T a b c
        (GBL.mk realGauge a b c
          (columnUnit a b source.1)
          (columnBasis (a + b) c source.2 sourceBasis)) =
      ∑ target : TargetFrame a b c,
        ∑ targetBasis : Fin (realRepDim (a + b + c).val),
          ((connectorLinearCoeff a b c target.1.val target.2.val
            source.1.val source.2.val targetBasis.val sourceBasis.val : ℤ) : ℝ) •
            GBR.mk realGauge a b c
              (columnUnit b c target.1)
              (columnBasisAssoc a b c target.2 targetBasis) := by
  rw [realRawConnector_on_basis_eq_sum]
  apply Finset.sum_congr rfl
  intro target _
  rw [← Equiv.sum_comp (assocBasisEquiv a b c)
    (fun targetBasis =>
      ((connectorLinearCoeff a b c target.1.val target.2.val
        source.1.val source.2.val targetBasis.val sourceBasis.val : ℤ) : ℝ) •
        GBR.mk realGauge a b c
          (columnUnit b c target.1)
          (columnBasis a (b + c) target.2 targetBasis))]
  apply Finset.sum_congr rfl
  intro targetBasis _
  rw [columnBasisAssoc_eq]
  rfl

/-! ## Exact fusion-slot columns -/

/-- Move a coefficient from the first singleton factor of a real `GBL`
generator to the left slot action on its second factor. -/
theorem gbl_mk_fsingle_move_real (a b c : ZMod 8)
    (row : Fin (realGauge.size a b).1 ⊕ Fin (realGauge.size a b).2)
    (x : (realGauge.D (a + b)).carrier)
    (v : FusionColumn (realGauge.fuse (a + b) c)) :
    GBL.mk realGauge a b c (fsingle (realGauge.fuse a b) row x) v =
      GBL.mk realGauge a b c (fsingle (realGauge.fuse a b) row 1) (x • v) := by
  rw [show fsingle (realGauge.fuse a b) row x =
      MulOpposite.op x •
        (fsingle (realGauge.fuse a b) row 1 :
          FusionColumn (realGauge.fuse a b)) from by
    funext z
    rw [fsingle_apply]
    change _ = (fsingle (realGauge.fuse a b) row 1 :
      FusionColumn (realGauge.fuse a b)) z * x
    rw [fsingle_apply]
    by_cases h : z = row
    · rw [if_pos h, if_pos h, one_mul]
    · rw [if_neg h, if_neg h, zero_mul]]
  exact RelTensor.mk_op_smul ℝ (realGauge.D (a + b)).carrier
    (FusionColumn (realGauge.fuse a b))
    (FusionColumn (realGauge.fuse (a + b) c)) x _ v

/-- One row of the left-slot action on a singleton fusion column. -/
theorem fusionLeft_basis_apply (a b : ZMod 8)
    (acting : Fin (realRepDim a.val))
    (target source : FusionTable.Index a b)
    (sourceBasis : Fin (realRepDim (a + b).val)) :
    (gaugeBasis a acting • columnBasis a b source sourceBasis :
        FusionColumn (realGauge.fuse a b))
        (FusionTable.frameIndex a b target) =
      ∑ targetBasis : Fin (realRepDim (a + b).val),
        ((fusionLeftSlotCoeff a b acting.val target.val targetBasis.val
          source.val sourceBasis.val : ℤ) : ℝ) •
          gaugeBasis (a + b) targetBasis := by
  change Fin (coefficientRank a) at acting
  change Fin (coefficientRank (a + b)) at sourceBasis
  rw [FusionColumn.slotLeft_smul_def]
  change Matrix.mulVec
      ((realGauge.fuse a b).toAlgEquiv
        (GradedTensorProduct.includeLeft (realGauge.D a).grading
          (realGauge.D b).grading (gaugeBasis a acting)))
      (Pi.single (FusionTable.frameIndex a b source)
        (realRepBasis (a + b) sourceBasis))
      (FusionTable.frameIndex a b target) = _
  rw [Matrix.mulVec_single]
  change FusionTableLaws.semanticFusionEntry a b target source
      (gaugeBasis a acting) 1 * realRepBasis (a + b) sourceBasis = _
  unfold gaugeBasis
  rw [← Coeff.semantic_one b]
  rw [← rawSemantic_coefficientBasis a acting,
    ← rawSemantic_coefficientBasis (a + b) sourceBasis,
    ← FusionTableLaws.semantic_fusionCoefficient_eq_semanticEntry,
    ← Coeff.semantic_mul]
  change semanticCoeff (a + b)
      (Coeff.mul (a + b)
        (FusionTable.fusionCoefficient a b target source
          (coefficientBasis a acting) (Coeff.one b))
        (coefficientBasis (a + b) sourceBasis)) = _
  rw [semanticCoeff_eq_sum]
  apply Finset.sum_congr rfl
  intro targetBasis _
  rw [fusionLeftSlotCoeff_cast a b acting target source
    targetBasis sourceBasis, coefficientBasis_unit]
  exact rawBasis_smul_eq_gaugeBasis_smul (a + b) targetBasis _

/-- One row of the right-slot action on a singleton fusion column. -/
theorem fusionRight_basis_apply (a b : ZMod 8)
    (acting : Fin (realRepDim b.val))
    (target source : FusionTable.Index a b)
    (sourceBasis : Fin (realRepDim (a + b).val)) :
    (gaugeBasis b acting • columnBasis a b source sourceBasis :
        FusionColumn (realGauge.fuse a b))
        (FusionTable.frameIndex a b target) =
      ∑ targetBasis : Fin (realRepDim (a + b).val),
        ((fusionRightSlotCoeff a b acting.val target.val targetBasis.val
          source.val sourceBasis.val : ℤ) : ℝ) •
          gaugeBasis (a + b) targetBasis := by
  change Fin (coefficientRank b) at acting
  change Fin (coefficientRank (a + b)) at sourceBasis
  rw [FusionColumn.slotRight_smul_def]
  change Matrix.mulVec
      ((realGauge.fuse a b).toAlgEquiv
        (GradedTensorProduct.includeRight (realGauge.D a).grading
          (realGauge.D b).grading (gaugeBasis b acting)))
      (Pi.single (FusionTable.frameIndex a b source)
        (realRepBasis (a + b) sourceBasis))
      (FusionTable.frameIndex a b target) = _
  rw [Matrix.mulVec_single]
  change FusionTableLaws.semanticFusionEntry a b target source
      1 (gaugeBasis b acting) * realRepBasis (a + b) sourceBasis = _
  unfold gaugeBasis
  rw [← Coeff.semantic_one a]
  rw [← rawSemantic_coefficientBasis b acting,
    ← rawSemantic_coefficientBasis (a + b) sourceBasis,
    ← FusionTableLaws.semantic_fusionCoefficient_eq_semanticEntry,
    ← Coeff.semantic_mul]
  change semanticCoeff (a + b)
      (Coeff.mul (a + b)
        (FusionTable.fusionCoefficient a b target source
          (Coeff.one a) (coefficientBasis b acting))
        (coefficientBasis (a + b) sourceBasis)) = _
  rw [semanticCoeff_eq_sum]
  apply Finset.sum_congr rfl
  intro targetBasis _
  rw [fusionRightSlotCoeff_cast a b acting target source
    targetBasis sourceBasis, coefficientBasis_unit]
  exact rawBasis_smul_eq_gaugeBasis_smul (a + b) targetBasis _

/-- Full finite-column expansion of the left slot action. -/
theorem fusionLeft_basis (a b : ZMod 8)
    (acting : Fin (realRepDim a.val))
    (source : FusionTable.Index a b)
    (sourceBasis : Fin (realRepDim (a + b).val)) :
    (gaugeBasis a acting • columnBasis a b source sourceBasis :
        FusionColumn (realGauge.fuse a b)) =
      ∑ target : FusionTable.Index a b,
        ∑ targetBasis : Fin (realRepDim (a + b).val),
          ((fusionLeftSlotCoeff a b acting.val target.val targetBasis.val
            source.val sourceBasis.val : ℤ) : ℝ) •
            columnBasis a b target targetBasis := by
  funext x
  change Fin (realSize a b).1 ⊕ Fin (realSize a b).2 at x
  let target : FusionTable.Index a b := finSumFinEquiv x
  have hx : FusionTable.frameIndex a b target = x := by
    exact finSumFinEquiv.symm_apply_apply x
  rw [← hx, fusionLeft_basis_apply]
  let basisTerm (row : FusionTable.Index a b)
      (targetBasis : Fin (realRepDim (a + b).val)) :
      FusionColumn (realGauge.fuse a b) :=
    ((fusionLeftSlotCoeff a b acting.val row.val targetBasis.val
      source.val sourceBasis.val : ℤ) : ℝ) •
      columnBasis a b row targetBasis
  let rowTerm : FusionTable.Index a b →
      FusionColumn (realGauge.fuse a b) := fun row =>
    ∑ targetBasis, basisTerm row targetBasis
  change (∑ targetBasis : Fin (realRepDim (a + b).val),
      ((fusionLeftSlotCoeff a b acting.val target.val targetBasis.val
        source.val sourceBasis.val : ℤ) : ℝ) •
        gaugeBasis (a + b) targetBasis) =
    (∑ row, rowTerm row) (FusionTable.frameIndex a b target)
  have houter :
      ((∑ row, rowTerm row) : FusionColumn (realGauge.fuse a b))
          (FusionTable.frameIndex a b target) =
        ∑ row, rowTerm row (FusionTable.frameIndex a b target) :=
    Finset.sum_apply (FusionTable.frameIndex a b target) Finset.univ rowTerm
  rw [houter]
  have hinner (row : FusionTable.Index a b) :
      rowTerm row (FusionTable.frameIndex a b target) =
        ∑ targetBasis,
          basisTerm row targetBasis (FusionTable.frameIndex a b target) := by
    unfold rowTerm
    exact Finset.sum_apply (FusionTable.frameIndex a b target)
      Finset.univ (basisTerm row)
  rw [Finset.sum_eq_single target]
  · rw [hinner]
    unfold basisTerm
    apply Finset.sum_congr rfl
    intro targetBasis _
    rw [fusionColumn_smul_apply, columnBasis_apply_same]
  · intro other _ hne
    rw [hinner]
    unfold basisTerm
    apply Finset.sum_eq_zero
    intro targetBasis _
    rw [fusionColumn_smul_apply,
      columnBasis_apply_ne a b other target targetBasis hne, smul_zero]
  · exact fun h => absurd (Finset.mem_univ target) h

/-- Full finite-column expansion of the right slot action. -/
theorem fusionRight_basis (a b : ZMod 8)
    (acting : Fin (realRepDim b.val))
    (source : FusionTable.Index a b)
    (sourceBasis : Fin (realRepDim (a + b).val)) :
    (gaugeBasis b acting • columnBasis a b source sourceBasis :
        FusionColumn (realGauge.fuse a b)) =
      ∑ target : FusionTable.Index a b,
        ∑ targetBasis : Fin (realRepDim (a + b).val),
          ((fusionRightSlotCoeff a b acting.val target.val targetBasis.val
            source.val sourceBasis.val : ℤ) : ℝ) •
            columnBasis a b target targetBasis := by
  funext x
  change Fin (realSize a b).1 ⊕ Fin (realSize a b).2 at x
  let target : FusionTable.Index a b := finSumFinEquiv x
  have hx : FusionTable.frameIndex a b target = x := by
    exact finSumFinEquiv.symm_apply_apply x
  rw [← hx, fusionRight_basis_apply]
  let basisTerm (row : FusionTable.Index a b)
      (targetBasis : Fin (realRepDim (a + b).val)) :
      FusionColumn (realGauge.fuse a b) :=
    ((fusionRightSlotCoeff a b acting.val row.val targetBasis.val
      source.val sourceBasis.val : ℤ) : ℝ) •
      columnBasis a b row targetBasis
  let rowTerm : FusionTable.Index a b →
      FusionColumn (realGauge.fuse a b) := fun row =>
    ∑ targetBasis, basisTerm row targetBasis
  change (∑ targetBasis : Fin (realRepDim (a + b).val),
      ((fusionRightSlotCoeff a b acting.val target.val targetBasis.val
        source.val sourceBasis.val : ℤ) : ℝ) •
        gaugeBasis (a + b) targetBasis) =
    (∑ row, rowTerm row) (FusionTable.frameIndex a b target)
  have houter :
      ((∑ row, rowTerm row) : FusionColumn (realGauge.fuse a b))
          (FusionTable.frameIndex a b target) =
        ∑ row, rowTerm row (FusionTable.frameIndex a b target) :=
    Finset.sum_apply (FusionTable.frameIndex a b target) Finset.univ rowTerm
  rw [houter]
  have hinner (row : FusionTable.Index a b) :
      rowTerm row (FusionTable.frameIndex a b target) =
        ∑ targetBasis,
          basisTerm row targetBasis (FusionTable.frameIndex a b target) := by
    unfold rowTerm
    exact Finset.sum_apply (FusionTable.frameIndex a b target)
      Finset.univ (basisTerm row)
  rw [Finset.sum_eq_single target]
  · rw [hinner]
    unfold basisTerm
    apply Finset.sum_congr rfl
    intro targetBasis _
    rw [fusionColumn_smul_apply, columnBasis_apply_same]
  · intro other _ hne
    rw [hinner]
    unfold basisTerm
    apply Finset.sum_eq_zero
    intro targetBasis _
    rw [fusionColumn_smul_apply,
      columnBasis_apply_ne a b other target targetBasis hne, smul_zero]
  · exact fun h => absurd (Finset.mem_univ target) h

/-- Moving a canonical coefficient out of the first singleton factor of a
left ternary generator produces the exact left-slot kernel expansion. -/
theorem gbl_mk_basis_basis_eq_sum (a b c : ZMod 8)
    (firstRow : FusionTable.Index a b)
    (acting : Fin (realRepDim (a + b).val))
    (secondRow : FusionTable.Index (a + b) c)
    (sourceBasis : Fin (realRepDim (a + b + c).val)) :
    GBL.mk realGauge a b c
        (columnBasis a b firstRow acting)
        (columnBasis (a + b) c secondRow sourceBasis) =
      ∑ targetRow : FusionTable.Index (a + b) c,
        ∑ targetBasis : Fin (realRepDim (a + b + c).val),
          ((fusionLeftSlotCoeff (a + b) c acting.val targetRow.val
            targetBasis.val secondRow.val sourceBasis.val : ℤ) : ℝ) •
            GBL.mk realGauge a b c
              (columnUnit a b firstRow)
              (columnBasis (a + b) c targetRow targetBasis) := by
  rw [columnBasis, columnUnit,
    gbl_mk_fsingle_move_real a b c]
  rw [fusionLeft_basis]
  simp_rw [map_sum, map_smul]

/-- The second top edge after the first ternary reassociation.  Moving the
transported coefficient through the balanced tensor reduces the statement
to `fusionLeft_basis` before applying `gColumnCastFst`. -/
theorem topSecondInput_eq_sum (a b c d : ZMod 8)
    (firstRow : FusionTable.Index a (b + c))
    (acting : Fin (realRepDim (a + b + c).val))
    (lastRow : FusionTable.Index (a + b + c) d)
    (sourceBasis : Fin (realRepDim (a + b + c + d).val)) :
    GBL.mk realGauge a (b + c) d
        (columnBasisAssoc a b c firstRow acting)
        (gColumnCastFst ℝ realGauge d (_root_.add_assoc a b c)
          (columnBasis (a + b + c) d lastRow sourceBasis)) =
      ∑ targetRow : FusionTable.Index (a + b + c) d,
        ∑ targetBasis : Fin (realRepDim (a + b + c + d).val),
          ((fusionLeftSlotCoeff (a + b + c) d acting.val targetRow.val
            targetBasis.val lastRow.val sourceBasis.val : ℤ) : ℝ) •
            GBL.mk realGauge a (b + c) d
              (columnUnit a (b + c) firstRow)
              (columnBasis (a + (b + c)) d
                (fusionRowCastFst d (_root_.add_assoc a b c) targetRow)
                (fusionBasisCastFst d (_root_.add_assoc a b c)
                  targetBasis)) := by
  rw [columnBasisAssoc]
  rw [gbl_mk_fsingle_move_real a (b + c) d]
  rw [← gColumnCastFst_xslot]
  rw [fusionLeft_basis]
  simp_rw [map_sum, map_smul, gColumnCastFst_columnBasis]
  simp only [columnUnit]

/-! The right-slot analogue is used only at the final target column. -/

/-- Right-slot action on a target singleton column, in exact kernel form. -/
theorem target_right_basis_eq_sum (a b : ZMod 8)
    (acting : Fin (realRepDim b.val))
    (sourceRow : FusionTable.Index a b)
    (sourceBasis : Fin (realRepDim (a + b).val)) :
    (gaugeBasis b acting • columnBasis a b sourceRow sourceBasis :
        FusionColumn (realGauge.fuse a b)) =
      ∑ targetRow : FusionTable.Index a b,
        ∑ targetBasis : Fin (realRepDim (a + b).val),
          ((fusionRightSlotCoeff a b acting.val targetRow.val targetBasis.val
            sourceRow.val sourceBasis.val : ℤ) : ℝ) •
            columnBasis a b targetRow targetBasis :=
  fusionRight_basis a b acting sourceRow sourceBasis

/-! ## The fourfold source generator -/

/-- The semantic `GQ1` basis generator represented by a kernel source
coordinate.  The first two binary columns carry the unit coefficient; the
last column carries the selected total coefficient basis vector. -/
noncomputable def semanticSource (a b c d : ZMod 8)
    (source : QuadSource a b c d) : GQ1 ℝ realGauge a b c d :=
  RelTensor.mk ℝ (realGauge.D (a + b + c)).carrier
    (GBL realGauge a b c)
    (FusionColumn (realGauge.fuse (a + b + c) d))
    (GBL.mk realGauge a b c
      (columnUnit a b source.1.1)
      (columnUnit (a + b) c source.1.2))
    (columnBasis (a + b + c) d source.2.1 source.2.2)

/-! ## Native target observation -/

/-- Equality between the stored outer-target total and the natural native
right-associated total used by `gq4NativeCoord`. -/
theorem targetTotal_assoc (a b c d : ZMod 8) :
    a + (b + c + d) = a + (b + (c + d)) := by
  rw [_root_.add_assoc b c d]

/-- Transport a stored target coefficient index to the natural native total. -/
def targetBasisNative (a b c d : ZMod 8)
    (basis : Fin (coefficientRank (a + (b + c + d)))) :
    Fin (coefficientRank (a + (b + (c + d)))) :=
  Fin.cast
    (congrArg coefficientRank
      (targetTotal_assoc a b c d)) basis

/-- Transport the stored last binary row to the natural native outer
fusion frame. -/
def targetLastRowNative (a b c d : ZMod 8)
    (row : FusionTable.Index a (b + c + d)) :
    FusionTable.Index a (b + (c + d)) :=
  Fin.cast
    (congrArg (fun x : ZMod 8 => fusionRank a x)
      (_root_.add_assoc b c d)) row

/-- Equality recast of a singleton outer column, including its row and
coefficient indices. -/
private theorem fusionColumnCast_symm_columnBasis (a : ZMod 8)
    {x y : ZMod 8} (h : x = y)
    (row : FusionTable.Index a y)
    (basis : Fin (realRepDim (a + y).val)) :
    (fusionColumnCast ℝ realGauge a h).symm
        (columnBasis a y row basis) =
      columnBasis a x
        (Fin.cast (congrArg (fun z : ZMod 8 => fusionRank a z) h.symm) row)
        (Fin.cast (congrArg
          (fun z : ZMod 8 => realRepDim (a + z).val) h.symm) basis) := by
  subst y
  rfl

/-- The final outer-column recast sends a stored left-associated kernel
basis to the corresponding native right-associated basis. -/
theorem outerBasisCast (a b c d : ZMod 8)
    (row : FusionTable.Index a (b + c + d))
    (basis : Fin (realRepDim (a + (b + c + d)).val)) :
    (fusionColumnCast ℝ realGauge a (_root_.add_assoc b c d).symm).symm
        (columnBasis a (b + c + d) row basis) =
      columnBasis a (b + (c + d))
        (targetLastRowNative a b c d row)
        (targetBasisNative a b c d basis) := by
  exact fusionColumnCast_symm_columnBasis a
    (_root_.add_assoc b c d).symm row basis

/-- The canonical coefficient functional at a kernel target basis index. -/
noncomputable def targetCoeffCoord (a b c d : ZMod 8)
    (basis : Fin (coefficientRank (a + (b + c + d)))) :
    (realGauge.D (a + (b + (c + d)))).carrier →ₗ[ℝ] ℝ :=
  (realRepBasis (a + (b + (c + d)))).coord
    (targetBasisNative a b c d basis)

/-- The semantic target functional represented by a kernel target coordinate. -/
noncomputable def semanticObserve (a b c d : ZMod 8)
    (target : QuadTarget a b c d) : GQ4 ℝ realGauge a b c d →ₗ[ℝ] ℝ :=
  gq4NativeCoord ℝ realGauge a b c d
    (gbrNativeIndexEquiv ℝ realGauge b c d
      (FusionTable.frameIndex c d target.1.1,
        FusionTable.frameIndex b (c + d) target.1.2))
    (FusionTable.frameIndex a (b + (c + d))
      (targetLastRowNative a b c d target.2.1))
    (targetCoeffCoord a b c d target.2.2)

/-! ## Elementary coordinate identities -/

@[simp]
theorem targetCoeffCoord_basis (a b c d : ZMod 8)
    (basis : Fin (coefficientRank (a + (b + c + d)))) :
    targetCoeffCoord a b c d basis
        (realRepBasis (a + (b + (c + d)))
          (targetBasisNative a b c d basis)) = 1 := by
  show (realRepBasis (a + (b + (c + d)))).coord
      (targetBasisNative a b c d basis)
      (realRepBasis (a + (b + (c + d)))
        (targetBasisNative a b c d basis)) = 1
  rw [Module.Basis.coord_apply,
    Module.Basis.repr_self_apply, if_pos rfl]

/-- The target functional evaluates to one on the matching native target
generator.  This is the common endpoint normalization for both routes. -/
@[simp]
theorem semanticObserve_targetGenerator (a b c d : ZMod 8)
    (target : QuadTarget a b c d) :
    semanticObserve a b c d target
        (RelTensor.mk ℝ (realGauge.D (b + c + d)).carrier
          (GBR realGauge b c d)
          (FusionColumn (realGauge.fuse a (b + c + d)))
          (GBR.mk realGauge b c d
            (columnUnit c d target.1.1)
            (columnUnit b (c + d) target.1.2))
          (columnBasis a (b + c + d) target.2.1 target.2.2)) = 1 := by
  rw [semanticObserve, GaugeChi.gq4NativeCoord_mk]
  simp only [columnUnit]
  rw [GaugeChi.gbrNativeColumnEquiv_fsingle]
  rw [outerBasisCast]
  simp only [GaugeChi.fsingle_apply, if_true, one_smul]
  rw [columnBasis_apply_same, targetCoeffCoord_basis]

end RealPChiRouteBridge
end Superfusion.RMod.RawDCT
