import Superfusion.RMod.RawDCT.RealT

/-!
# Exact finite kernel for the real raw fourfold routes

This file is the integer coordinate evaluator underlying the two sides of
the raw pentagon.  It reads only the coefficient table of `realTData.hom`,
the coefficient table of `realCData.leftCoeff`, and the signed monomial
multiplication table of the real coefficient algebras.  In particular, it
does not read a `chi` table and it does not form an equality in `ℝ`.

The input and output coordinates use the parity-aligned route frames of
`ConstructiveRouteFrame.frameEquiv`.  `topCoeff` is the coefficient of
`GE3 ∘ GE2 ∘ GE1`; `botCoeff` is the coefficient of
`gq4Close ∘ GE5 ∘ GE4`.  The formulas are the finite-coordinate versions of
the already existing fourfold routes in `GaugeChi/QuadChase.lean`.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiKernel

open RModCoordinate
open RModCoordinate.FusionTable
open RMod.ConstructiveConnectorTable
open RMod.ConstructiveRouteFrame

/-! ## Finite frames and their flat encodings -/

/-- Total number of rows in one binary fusion frame. -/
def fusionRank (a b : ZMod 8) : ℕ :=
  (realSize a b).1 + (realSize a b).2

/-- Dimension of the canonical coefficient basis at one label. -/
def coefficientRank (a : ZMod 8) : ℕ := realRepDim a.val

/-- A source-frame row of a ternary connector. -/
abbrev SourceFrame (a b c : ZMod 8) : Type :=
  FusionTable.Index a b × FusionTable.Index (a + b) c

/-- A target-frame row of a ternary connector. -/
abbrev TargetFrame (a b c : ZMod 8) : Type :=
  FusionTable.Index b c × FusionTable.Index a (b + c)

/-- A basis coordinate of one binary fusion column. -/
abbrev ColumnCoordinate (a b : ZMod 8) : Type :=
  FusionTable.Index a b × Fin (coefficientRank (a + b))

/-- A basis generator at the source vertex of the fourfold comparison.

The factors are `((r_ab,r_(a+b)c),(r_(a+b+c)d,e_total))`. -/
abbrev QuadSource (a b c d : ZMod 8) : Type :=
  SourceFrame a b c × ColumnCoordinate (a + b + c) d

/-- A scalar coordinate at the target vertex of the fourfold comparison.

The factors are `((r_cd,r_b(c+d)),(r_a(b+c+d),e_total))`. -/
abbrev QuadTarget (a b c d : ZMod 8) : Type :=
  TargetFrame b c d × ColumnCoordinate a (b + c + d)

/-- Parity-aligned flattening of a ternary source frame. -/
def sourceFrameEquiv (a b c : ZMod 8) :
    SourceFrame a b c ≃
      Fin (((realSize a b).1 * (realSize (a + b) c).1 +
          (realSize a b).2 * (realSize (a + b) c).2) +
        ((realSize a b).1 * (realSize (a + b) c).2 +
          (realSize a b).2 * (realSize (a + b) c).1)) :=
  RMod.ConstructiveRouteFrame.frameEquiv (realSize a b).1 (realSize a b).2
    (realSize (a + b) c).1 (realSize (a + b) c).2

/-- Parity-aligned flattening of a ternary target frame. -/
def targetFrameEquiv (a b c : ZMod 8) :
    TargetFrame a b c ≃
      Fin (((realSize b c).1 * (realSize a (b + c)).1 +
          (realSize b c).2 * (realSize a (b + c)).2) +
        ((realSize b c).1 * (realSize a (b + c)).2 +
          (realSize b c).2 * (realSize a (b + c)).1)) :=
  RMod.ConstructiveRouteFrame.frameEquiv (realSize b c).1 (realSize b c).2
    (realSize a (b + c)).1 (realSize a (b + c)).2

/-- Number of parity-aligned source-frame rows. -/
def sourceFrameRank (a b c : ZMod 8) : ℕ :=
  ((realSize a b).1 * (realSize (a + b) c).1 +
      (realSize a b).2 * (realSize (a + b) c).2) +
    ((realSize a b).1 * (realSize (a + b) c).2 +
      (realSize a b).2 * (realSize (a + b) c).1)

/-- Number of parity-aligned target-frame rows. -/
def targetFrameRank (a b c : ZMod 8) : ℕ :=
  ((realSize b c).1 * (realSize a (b + c)).1 +
      (realSize b c).2 * (realSize a (b + c)).2) +
    ((realSize b c).1 * (realSize a (b + c)).2 +
      (realSize b c).2 * (realSize a (b + c)).1)

/-- Number of coefficient coordinates in one fusion column. -/
def columnCoordinateRank (a b : ZMod 8) : ℕ :=
  fusionRank a b * coefficientRank (a + b)

/-- Number of basis generators at the fourfold source vertex. -/
def quadSourceRank (a b c d : ZMod 8) : ℕ :=
  sourceFrameRank a b c * columnCoordinateRank (a + b + c) d

/-- Number of scalar coordinates at the fourfold target vertex. -/
def quadTargetRank (a b c d : ZMod 8) : ℕ :=
  targetFrameRank b c d * columnCoordinateRank a (b + c + d)

/-- Row/coefficient flattening of one binary fusion column. -/
def columnCoordinateEquiv (a b : ZMod 8) :
    ColumnCoordinate a b ≃ Fin (columnCoordinateRank a b) :=
  finProdFinEquiv

/-- The complete source basis in the deterministic generator-scan order. -/
def quadSourceEquiv (a b c d : ZMod 8) :
    QuadSource a b c d ≃ Fin (quadSourceRank a b c d) :=
  ((sourceFrameEquiv a b c).prodCongr
      (columnCoordinateEquiv (a + b + c) d)).trans finProdFinEquiv

/-- The complete target basis in deterministic coordinate-scan order. -/
def quadTargetEquiv (a b c d : ZMod 8) :
    QuadTarget a b c d ≃ Fin (quadTargetRank a b c d) :=
  ((targetFrameEquiv b c d).prodCongr
      (columnCoordinateEquiv a (b + c + d))).trans finProdFinEquiv

/-- Decode a bounded flat source index. -/
def sourceOfFlat (a b c d : ZMod 8)
    (i : Fin (quadSourceRank a b c d)) : QuadSource a b c d :=
  (quadSourceEquiv a b c d).symm i

/-- Decode a bounded flat target index. -/
def targetOfFlat (a b c d : ZMod 8)
    (i : Fin (quadTargetRank a b c d)) : QuadTarget a b c d :=
  (quadTargetEquiv a b c d).symm i

/- The following projections keep later semantic bridge statements readable. -/

def sourceABRow {a b c d : ZMod 8} (s : QuadSource a b c d) := s.1.1
def sourceABCRow {a b c d : ZMod 8} (s : QuadSource a b c d) := s.1.2
def sourceLastRow {a b c d : ZMod 8} (s : QuadSource a b c d) := s.2.1
def sourceLastBasis {a b c d : ZMod 8} (s : QuadSource a b c d) := s.2.2

def targetCDRow {a b c d : ZMod 8} (t : QuadTarget a b c d) := t.1.1
def targetBCDRow {a b c d : ZMod 8} (t : QuadTarget a b c d) := t.1.2
def targetLastRow {a b c d : ZMod 8} (t : QuadTarget a b c d) := t.2.1
def targetLastBasis {a b c d : ZMod 8} (t : QuadTarget a b c d) := t.2.2

/-- Flat encoding used by the exact source-generator scan.  The route frame
is flattened first in parity-aligned order, then the final fusion row, then
the total coefficient basis index. -/
def sourceFlat (a b c d : ZMod 8) (s : QuadSource a b c d) : ℕ :=
  (sourceFrameEquiv a b c s.1).val *
      columnCoordinateRank (a + b + c) d +
    s.2.1.val * coefficientRank (a + b + c + d) + s.2.2.val

/-- Flat target ordering: parity-aligned target frame, final fusion row,
then total coefficient basis index. -/
def targetFlat (a b c d : ZMod 8) (t : QuadTarget a b c d) : ℕ :=
  (targetFrameEquiv b c d t.1).val *
      columnCoordinateRank a (b + c + d) +
    t.2.1.val * coefficientRank (a + (b + c + d)) + t.2.2.val

private theorem finProdFinEquiv_val {m n : ℕ} (x : Fin m × Fin n) :
    (finProdFinEquiv x).val = x.2.val + n * x.1.val :=
  rfl

theorem sourceFlat_eq (a b c d : ZMod 8) (s : QuadSource a b c d) :
    sourceFlat a b c d s = (quadSourceEquiv a b c d s).val := by
  change sourceFlat a b c d s =
    (finProdFinEquiv
      (sourceFrameEquiv a b c s.1, finProdFinEquiv s.2)).val
  rw [finProdFinEquiv_val, finProdFinEquiv_val]
  simp only [sourceFlat, columnCoordinateRank, fusionRank]
  ring

theorem targetFlat_eq (a b c d : ZMod 8) (t : QuadTarget a b c d) :
    targetFlat a b c d t = (quadTargetEquiv a b c d t).val := by
  change targetFlat a b c d t =
    (finProdFinEquiv
      (targetFrameEquiv b c d t.1, finProdFinEquiv t.2)).val
  rw [finProdFinEquiv_val, finProdFinEquiv_val]
  simp only [targetFlat, columnCoordinateRank, fusionRank]
  ring

@[simp]
theorem sourceOfFlat_encode (a b c d : ZMod 8) (s : QuadSource a b c d) :
    sourceOfFlat a b c d (quadSourceEquiv a b c d s) = s :=
  (quadSourceEquiv a b c d).left_inv s

@[simp]
theorem targetOfFlat_encode (a b c d : ZMod 8) (t : QuadTarget a b c d) :
    targetOfFlat a b c d (quadTargetEquiv a b c d t) = t :=
  (quadTargetEquiv a b c d).left_inv t

/-! ## Integer coefficient-algebra and fusion kernels -/

/-- Finite integer sum over the natural interval `[0,n)`. -/
def sumRange (n : ℕ) (f : ℕ → ℤ) : ℤ :=
  ((List.range n).map f).sum

/-- `sumRange` is the ordinary sum over the corresponding `Fin` type. -/
theorem sumRange_eq_sumFin (n : ℕ) (f : ℕ → ℤ) :
    sumRange n f = ∑ i : Fin n, f i.val := by
  rw [sumRange, ← Superfusion.sum_range_eq_listSum]
  exact (Fin.sum_univ_eq_sum_range f n).symm

/-- The standard coordinate basis vector in a raw coefficient algebra. -/
def coefficientBasis (a : ZMod 8) (i : Fin (coefficientRank a)) : Coeff a :=
  fun j => if j = i then 1 else 0

/-- Index of the unit in every canonical coefficient basis. -/
def coefficientUnitIndex (a : ZMod 8) : Fin (coefficientRank a) :=
  ⟨0, realRepDim_pos a.val⟩

/-- Coefficient of `e_target` in `x * e_source`, where `x` is presented in
the canonical signed monomial basis of the `m`-th coefficient algebra. -/
def leftMulBasisCoeff (m : ℕ) (x : ℕ → ℤ)
    (source target : ℕ) : ℤ :=
  sumRange (realRepDim m) fun i =>
    let j := realCoN m i target
    if j = source then realSignN m i j * x i else 0

/-- Casting the integer convolution to `ℝ` gives the stored executable
coefficient-algebra multiplication on a basis vector. -/
theorem leftMulBasisCoeff_cast (a : ZMod 8) (x : ℕ → ℤ)
    (source target : Fin (coefficientRank a)) :
    ((leftMulBasisCoeff a.val x source.val target.val : ℤ) : ℝ) =
      Coeff.mul a (fun i => (x i.val : ℝ)) (coefficientBasis a source) target := by
  rw [leftMulBasisCoeff, sumRange_eq_sumFin]
  simp only [Int.cast_sum, Coeff.mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [realCoN, realSignN, realRepMulIdx, realRepMulSign,
    natCo_apply, natTable2_apply, coefficientBasis]
  by_cases h : realRepMulIdxAux a.val i target = source
  · rw [if_pos (congrArg Fin.val h), if_pos h]
    push_cast
    ring
  · rw [if_neg (fun hv => h (Fin.ext hv)), if_neg h]
    simp

/-- One integer coefficient of the raw binary fusion matrix on a pair of
coefficient-basis vectors.  All indexing conventions are the literal ones
of `FusionTable.fusionCoefficient`. -/
def fusionBasisEntry (a b : ZMod 8)
    (targetRow sourceRow leftBasis rightBasis outputBasis : ℕ) : ℤ :=
  FusionTable.entry a b
    (outputBasis + coefficientRank (a + b) *
      (sourceRow + fusionRank a b * targetRow))
    (rightBasis + coefficientRank b * leftBasis)

/-- A basis-pair evaluation of the executable raw fusion coefficient is the
cast of the integer table entry used by this kernel. -/
theorem fusionCoefficient_basis (a b : ZMod 8)
    (target source : FusionTable.Index a b)
    (left : Fin (coefficientRank a)) (right : Fin (coefficientRank b))
    (output : Fin (coefficientRank (a + b))) :
    fusionCoefficient a b target source
        (coefficientBasis a left) (coefficientBasis b right) output =
      (fusionBasisEntry a b target.val source.val left.val right.val output.val : ℝ) := by
  simp [fusionCoefficient, coefficientBasis, fusionBasisEntry,
    outputPosition, inputPosition, coefficientRank, fusionRank]

/-- Matrix coefficient of the left slot action on a fusion column. -/
def fusionLeftSlotCoeff (a b : ZMod 8) (actingBasis : ℕ)
    (targetRow targetBasis sourceRow sourceBasis : ℕ) : ℤ :=
  leftMulBasisCoeff (a + b).val
    (fun h => fusionBasisEntry a b targetRow sourceRow actingBasis 0 h)
    sourceBasis targetBasis

/-- Matrix coefficient of the right slot action on a fusion column. -/
def fusionRightSlotCoeff (a b : ZMod 8) (actingBasis : ℕ)
    (targetRow targetBasis sourceRow sourceBasis : ℕ) : ℤ :=
  leftMulBasisCoeff (a + b).val
    (fun h => fusionBasisEntry a b targetRow sourceRow 0 actingBasis h)
    sourceBasis targetBasis

/-- The integer left-slot kernel casts to the actual `realCData.leftCoeff`
matrix coefficient on coordinate basis vectors. -/
theorem fusionLeftSlotCoeff_cast (a b : ZMod 8)
    (acting : Fin (coefficientRank a))
    (target source : FusionTable.Index a b)
    (targetBasis sourceBasis : Fin (coefficientRank (a + b))) :
    ((fusionLeftSlotCoeff a b acting.val target.val targetBasis.val
        source.val sourceBasis.val : ℤ) : ℝ) =
      Coeff.mul (a + b)
        (fusionCoefficient a b target source
          (coefficientBasis a acting)
          (coefficientBasis b (coefficientUnitIndex b)))
        (coefficientBasis (a + b) sourceBasis) targetBasis := by
  rw [fusionLeftSlotCoeff, leftMulBasisCoeff_cast]
  congr 1
  funext h
  exact (fusionCoefficient_basis a b target source acting
    (coefficientUnitIndex b) h).symm

/-- The integer right-slot kernel casts to the actual `realCData.leftCoeff`
matrix coefficient on coordinate basis vectors. -/
theorem fusionRightSlotCoeff_cast (a b : ZMod 8)
    (acting : Fin (coefficientRank b))
    (target source : FusionTable.Index a b)
    (targetBasis sourceBasis : Fin (coefficientRank (a + b))) :
    ((fusionRightSlotCoeff a b acting.val target.val targetBasis.val
        source.val sourceBasis.val : ℤ) : ℝ) =
      Coeff.mul (a + b)
        (fusionCoefficient a b target source
          (coefficientBasis a (coefficientUnitIndex a))
          (coefficientBasis b acting))
        (coefficientBasis (a + b) sourceBasis) targetBasis := by
  rw [fusionRightSlotCoeff, leftMulBasisCoeff_cast]
  congr 1
  funext h
  exact (fusionCoefficient_basis a b target source
    (coefficientUnitIndex a) acting h).symm

/-- Natural-number formula for a source route-frame position. -/
def sourceFramePosition (a b c : ZMod 8) (outer inner : ℕ) : ℕ :=
  collapsePositionNat (realSize a b).1 (realSize a b).2
    (realSize (a + b) c).1 (realSize (a + b) c).2 outer inner

/-- Natural-number formula for a target route-frame position. -/
def targetFramePosition (a b c : ZMod 8) (outer inner : ℕ) : ℕ :=
  collapsePositionNat (realSize b c).1 (realSize b c).2
    (realSize a (b + c)).1 (realSize a (b + c)).2 outer inner

theorem sourceFramePosition_eq_realTLeftPosition (a b c : ZMod 8)
    (outer : FusionTable.Index a b)
    (inner : FusionTable.Index (a + b) c) :
    sourceFramePosition a b c outer.val inner.val =
      realTLeftPosition a b c outer inner := by
  unfold sourceFramePosition realTLeftPosition
  rw [RMod.ConstructiveRouteFrame.frameEquiv_val]

theorem targetFramePosition_eq_realTRightPosition (a b c : ZMod 8)
    (outer : FusionTable.Index b c)
    (inner : FusionTable.Index a (b + c)) :
    targetFramePosition a b c outer.val inner.val =
      realTRightPosition a b c outer inner := by
  unfold targetFramePosition realTRightPosition
  rw [RMod.ConstructiveRouteFrame.frameEquiv_val]

/-- Scalar matrix coefficient of the stored raw forward connector.

`forwardCoeff` stores a matrix over the coefficient algebra.  The executable
map `realTData.hom` acts by left multiplication by that entry, so this
function expands precisely that multiplication in the signed monomial
basis. -/
def connectorLinearCoeff (a b c : ZMod 8)
    (targetOuter targetInner sourceOuter sourceInner : ℕ)
    (targetBasis sourceBasis : ℕ) : ℤ :=
  leftMulBasisCoeff (a + b + c).val
    (fun h => coeffGet (forwardCoeff a b c)
      (targetFramePosition a b c targetOuter targetInner)
      (sourceFramePosition a b c sourceOuter sourceInner) h)
    sourceBasis targetBasis

/-- The integer connector kernel casts to one scalar matrix coefficient of
the executable map `realTData.hom`. -/
theorem connectorLinearCoeff_cast (a b c : ZMod 8)
    (target : TargetFrame a b c) (source : SourceFrame a b c)
    (targetBasis sourceBasis : Fin (coefficientRank (a + b + c))) :
    ((connectorLinearCoeff a b c target.1.val target.2.val
        source.1.val source.2.val targetBasis.val sourceBasis.val : ℤ) : ℝ) =
      Coeff.mul (a + b + c)
        (realTForwardEntry a b c target.1 target.2 source.1 source.2)
        (coefficientBasis (a + b + c) sourceBasis) targetBasis := by
  rw [connectorLinearCoeff, leftMulBasisCoeff_cast]
  congr 1
  funext h
  simp only [realTForwardEntry]
  rw [← sourceFramePosition_eq_realTLeftPosition,
    ← targetFramePosition_eq_realTRightPosition]

/-- Parity of a row in the even-first binary fusion frame, as a natural bit. -/
def rowParityNat (a b : ZMod 8) (row : ℕ) : ℕ :=
  if row < (realSize a b).1 then 0 else 1

/-- Parity of the stored raw connector, as a natural bit. -/
def connectorParityNat (a b c : ZMod 8) : ℕ :=
  (realTData.parity a b c).val

/-- The integer Koszul sign of a natural parity exponent. -/
def koszulSign (n : ℕ) : ℤ := if n % 2 = 0 then 1 else -1

/-! ## The two exact fourfold route coefficients -/

/-- One scalar coordinate of `GE3 ∘ GE2 ∘ GE1` on one source generator.

The nested sums follow the three existing top edges in order.  Zero tests
only short-circuit sparse table entries; they do not alter the formula. -/
def topCoeff (a b c d : ZMod 8)
    (src : QuadSource a b c d) (dst : QuadTarget a b c d) : ℤ :=
  let totalDim := coefficientRank (a + b + c + d)
  let d1 := coefficientRank (a + b + c)
  let d3 := coefficientRank (b + c + d)
  let srcAB := src.1.1.val
  let srcABC := src.1.2.val
  let srcLastRow := src.2.1.val
  let srcLastBasis := src.2.2.val
  let dstCD := dst.1.1.val
  let dstBCD := dst.1.2.val
  let dstLastRow := dst.2.1.val
  let dstLastBasis := dst.2.2.val
  sumRange (fusionRank b c) fun rowBC =>
    sumRange (fusionRank a (b + c)) fun rowA_BC =>
      sumRange d1 fun basis1 =>
        let edge1 := connectorLinearCoeff a b c
          rowBC rowA_BC srcAB srcABC basis1 0
        if edge1 = 0 then 0 else
          sumRange (fusionRank (a + b + c) d) fun rowLast1 =>
            sumRange totalDim fun basis2 =>
              let slot1 := fusionLeftSlotCoeff (a + b + c) d basis1
                rowLast1 basis2 srcLastRow srcLastBasis
              if slot1 = 0 then 0 else
                let edge2Sign := koszulSign
                  (connectorParityNat a (b + c) d * rowParityNat b c rowBC)
                sumRange (fusionRank (b + c) d) fun rowBC_D =>
                  sumRange (fusionRank a (b + c + d)) fun rowA_BCD =>
                    sumRange totalDim fun basis3 =>
                      let edge2 := connectorLinearCoeff a (b + c) d
                        rowBC_D rowA_BCD rowA_BC rowLast1 basis3 basis2
                      if edge2 = 0 then 0 else
                        sumRange d3 fun basis4 =>
                          let edge3 := connectorLinearCoeff b c d
                            dstCD dstBCD rowBC rowBC_D basis4 0
                          if edge3 = 0 then 0 else
                            let slot3 := fusionRightSlotCoeff a (b + c + d) basis4
                              dstLastRow dstLastBasis rowA_BCD basis3
                            edge1 * slot1 * edge2Sign * edge2 * edge3 * slot3

/-- One scalar coordinate of `gq4Close ∘ GE5 ∘ GE4` on the same source
generator.  `gq4Close` only refactors the final target frame, so no further
numerical coefficient occurs after the fifth edge. -/
def botCoeff (a b c d : ZMod 8)
    (src : QuadSource a b c d) (dst : QuadTarget a b c d) : ℤ :=
  let totalDim := coefficientRank (a + b + c + d)
  let srcAB := src.1.1.val
  let srcABC := src.1.2.val
  let srcLastRow := src.2.1.val
  let srcLastBasis := src.2.2.val
  let dstCD := dst.1.1.val
  let dstBCD := dst.1.2.val
  let dstLastRow := dst.2.1.val
  let dstLastBasis := dst.2.2.val
  let sourceParity := rowParityNat a b srcAB
  let edge4Sign := koszulSign
    (connectorParityNat (a + b) c d * sourceParity)
  let edge5Sign := koszulSign
    (rowParityNat c d dstCD *
      (connectorParityNat a b (c + d) + sourceParity))
  edge4Sign * edge5Sign *
    sumRange (fusionRank (a + b) (c + d)) fun rowAB_CD =>
      sumRange totalDim fun basis4 =>
        let edge4 := connectorLinearCoeff (a + b) c d
          dstCD rowAB_CD srcABC srcLastRow basis4 srcLastBasis
        if edge4 = 0 then 0 else
          let edge5 := connectorLinearCoeff a b (c + d)
            dstBCD dstLastRow srcAB rowAB_CD dstLastBasis basis4
          edge4 * edge5

/-! ## Closed checks at the genuinely nontrivial quaternion quadruple -/

private def source4444 : QuadSource 4 4 4 4 :=
  ((⟨0, by decide⟩, ⟨0, by decide⟩),
    (⟨0, by decide⟩, ⟨0, by decide⟩))

private def target4444 : QuadTarget 4 4 4 4 :=
  ((⟨0, by decide⟩, ⟨0, by decide⟩),
    (⟨0, by decide⟩, ⟨0, by decide⟩))

/-- The top quaternion route recombines four basis summands. -/
example : topCoeff 4 4 4 4 source4444 target4444 = 4 := by
  decide +kernel

/-- The bottom route at the same source and coordinate is the unit. -/
example : botCoeff 4 4 4 4 source4444 target4444 = 1 := by
  decide +kernel

end RealPChiKernel
end Superfusion.RMod.RawDCT
