import Superfusion.GaugeChi.RealGaugeTables
import Superfusion.RMod.RawDCT.DyadicReal
import Superfusion.RMod.RawDCT.RealPChiKernel

/-!
# Exact certificate interface for the real raw pentagon table

This file contains only the small, reusable checker used by the generated
certificate leaves.  A witness selects a flat source generator and one flat
target coordinate.  The checker decodes both indices through the route-frame
equivalences of `RealPChiKernel`, verifies that the bottom coefficient is
nonzero, and compares the actual top/bottom coefficients with the frozen
dyadic table in exact rational arithmetic.

The packed witness bytes are search hints only.  Every numerical assertion is
recomputed by Lean from `realTData.hom` and checked by the kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

open GaugeChi
open RealPChiKernel

/-! ## Packed target-coordinate witnesses -/

/-- Unsigned byte lookup for packed flat target indices. -/
def packedByteAt (table index : ℕ) : ℕ :=
  (table >>> (8 * index)) % 256

/-- Lexicographic index of the three unfixed labels in one certificate leaf. -/
def leafIndex (b c d : ZMod 8) : ℕ :=
  (b.val * 8 + c.val) * 8 + d.val

/-- Lexicographic index of the two unfixed labels in an `(a,b)` leaf. -/
def pairLeafIndex (c d : ZMod 8) : ℕ :=
  c.val * 8 + d.val

/-- Exhaustive label cases used only to assemble independently checked
certificate leaves. -/
theorem label_cases (a : ZMod 8) :
    a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨
      a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 := by
  revert a
  decide +kernel

/-- Select one of eight data values by a group label. -/
def selectLabel (a : ZMod 8)
    (x0 x1 x2 x3 x4 x5 x6 x7 : ℕ) : ℕ :=
  if a = 0 then x0
  else if a = 1 then x1
  else if a = 2 then x2
  else if a = 3 then x3
  else if a = 4 then x4
  else if a = 5 then x5
  else if a = 6 then x6
  else x7

/-! ## Exact pointwise checker -/

/-- Exact rational value of the frozen dyadic entry at four additive labels. -/
def tableValue (a b c d : ZMod 8) : ℚ :=
  dyadicRatValue <| realLeanChiTable
    (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
    (Multiplicative.ofAdd c) (Multiplicative.ofAdd d)

/-- A source/target pair certifies one table entry when both indices are in
range, the selected bottom coefficient is nonzero, and the actual top
coefficient is the frozen table value times the actual bottom coefficient. -/
def IsExactWitness (a b c d : ZMod 8)
    (sourceIndex targetIndex : ℕ) : Prop :=
  if hs : sourceIndex < quadSourceRank a b c d then
    if ht : targetIndex < quadTargetRank a b c d then
      let source := sourceOfFlat a b c d ⟨sourceIndex, hs⟩
      let target := targetOfFlat a b c d ⟨targetIndex, ht⟩
      botCoeff a b c d source target ≠ 0 ∧
        (topCoeff a b c d source target : ℚ) =
          tableValue a b c d * (botCoeff a b c d source target : ℚ)
    else False
  else False

/-- The exact witness condition is executable, including both bound checks. -/
instance (a b c d : ZMod 8) (sourceIndex targetIndex : ℕ) :
    Decidable (IsExactWitness a b c d sourceIndex targetIndex) := by
  unfold IsExactWitness
  infer_instance

/-- Assemble eight independently checked `(a,b)` leaves without evaluating
any fourfold coefficient again. -/
theorem assembleWitness (a b c d : ZMod 8)
    (x0 x1 x2 x3 x4 x5 x6 x7 : ℕ)
    (h0 : IsExactWitness a 0 c d 0 x0)
    (h1 : IsExactWitness a 1 c d 0 x1)
    (h2 : IsExactWitness a 2 c d 0 x2)
    (h3 : IsExactWitness a 3 c d 0 x3)
    (h4 : IsExactWitness a 4 c d 0 x4)
    (h5 : IsExactWitness a 5 c d 0 x5)
    (h6 : IsExactWitness a 6 c d 0 x6)
    (h7 : IsExactWitness a 7 c d 0 x7) :
    IsExactWitness a b c d 0 (selectLabel b x0 x1 x2 x3 x4 x5 x6 x7) := by
  rcases label_cases b with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · unfold selectLabel
    rw [if_pos rfl]
    exact h0
  · unfold selectLabel
    rw [if_neg (by decide), if_pos rfl]
    exact h1
  · unfold selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact h2
  · unfold selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact h3
  · unfold selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_pos rfl]
    exact h4
  · unfold selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact h5
  · unfold selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact h6
  · unfold selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide)]
    exact h7

/-! ## Deterministic typed witnesses and their laws -/

/-- The source byte of a successful certificate is in range. -/
theorem IsExactWitness.sourceIndex_lt {a b c d : ZMod 8}
    {sourceIndex targetIndex : ℕ}
    (h : IsExactWitness a b c d sourceIndex targetIndex) :
    sourceIndex < quadSourceRank a b c d := by
  unfold IsExactWitness at h
  split at h
  · assumption
  · contradiction

/-- The target byte of a successful certificate is in range. -/
theorem IsExactWitness.targetIndex_lt {a b c d : ZMod 8}
    {sourceIndex targetIndex : ℕ}
    (h : IsExactWitness a b c d sourceIndex targetIndex) :
    targetIndex < quadTargetRank a b c d := by
  unfold IsExactWitness at h
  split at h
  · split at h
    · assumption
    · contradiction
  · contradiction

/-- Deterministic typed source selected by a checked flat certificate. -/
def IsExactWitness.source {a b c d : ZMod 8}
    {sourceIndex targetIndex : ℕ}
    (h : IsExactWitness a b c d sourceIndex targetIndex) :
    QuadSource a b c d :=
  sourceOfFlat a b c d ⟨sourceIndex, h.sourceIndex_lt⟩

/-- Deterministic typed target selected by a checked flat certificate. -/
def IsExactWitness.target {a b c d : ZMod 8}
    {sourceIndex targetIndex : ℕ}
    (h : IsExactWitness a b c d sourceIndex targetIndex) :
    QuadTarget a b c d :=
  targetOfFlat a b c d ⟨targetIndex, h.targetIndex_lt⟩

/-- The deterministically decoded source retains its packed flat index. -/
theorem IsExactWitness.sourceFlat {a b c d : ZMod 8}
    {sourceIndex targetIndex : ℕ}
    (h : IsExactWitness a b c d sourceIndex targetIndex) :
    RealPChiKernel.sourceFlat a b c d h.source = sourceIndex := by
  rw [RealPChiKernel.sourceFlat_eq]
  exact congrArg Fin.val <|
    (quadSourceEquiv a b c d).apply_symm_apply
      ⟨sourceIndex, h.sourceIndex_lt⟩

/-- The deterministically decoded target retains its packed flat index. -/
theorem IsExactWitness.targetFlat {a b c d : ZMod 8}
    {sourceIndex targetIndex : ℕ}
    (h : IsExactWitness a b c d sourceIndex targetIndex) :
    RealPChiKernel.targetFlat a b c d h.target = targetIndex := by
  rw [RealPChiKernel.targetFlat_eq]
  exact congrArg Fin.val <|
    (quadTargetEquiv a b c d).apply_symm_apply
      ⟨targetIndex, h.targetIndex_lt⟩

/-- The actual bottom-route coefficient at the decoded coordinate is nonzero. -/
theorem IsExactWitness.bottom_ne_zero {a b c d : ZMod 8}
    {sourceIndex targetIndex : ℕ}
    (h : IsExactWitness a b c d sourceIndex targetIndex) :
    botCoeff a b c d h.source h.target ≠ 0 := by
  unfold IsExactWitness at h
  split at h
  · split at h
    · simpa [IsExactWitness.source, IsExactWitness.target] using h.1
    · contradiction
  · contradiction

/-- The actual top coefficient has the frozen dyadic ratio at the decoded
coordinate. -/
theorem IsExactWitness.top_eq {a b c d : ZMod 8}
    {sourceIndex targetIndex : ℕ}
    (h : IsExactWitness a b c d sourceIndex targetIndex) :
    (topCoeff a b c d h.source h.target : ℚ) =
      tableValue a b c d * (botCoeff a b c d h.source h.target : ℚ) := by
  unfold IsExactWitness at h
  split at h
  · split at h
    · simpa [IsExactWitness.source, IsExactWitness.target] using h.2
    · contradiction
  · contradiction

end RealPChiCertificate
end Superfusion.RMod.RawDCT
