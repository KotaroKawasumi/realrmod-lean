/-
Superfusion / RMod / Constructive / ConnectorTableRouteInverseLaws

Route-frame form of the raw connector inverse certificates.  The frozen
integer table remains the sole source of coefficients.  This module only
reindexes its flat rows by the two raw fusion-row pairs and casts the checked
integer convolution to the coordinate algebra.
-/
import Superfusion.RMod.Constructive.CoefficientData
import Superfusion.RMod.Constructive.ConnectorTableRawInverseLaws
import Superfusion.RMod.Constructive.ConnectorTableRankLaws
import Superfusion.RMod.Constructive.FusionTableData
import Superfusion.RMod.Constructive.RouteFrame

set_option autoImplicit false

namespace Superfusion
namespace RModCoordinate
namespace ConnectorTableLaws

open RMod.ConstructiveConnectorTable
open RMod.ConstructiveRouteFrame

/-! ## Raw route pairs and their flat connector positions

The two parenthesizations generally have different pair types.  Their total
cardinalities nevertheless equal the single flat table dimension `sigma`.
-/

/-- A row of the left-associated raw fusion route. -/
abbrev LeftPair (a b c : ZMod 8) : Type :=
  FusionTable.Index a b × FusionTable.Index (a + b) c

/-- A row of the right-associated raw fusion route. -/
abbrev RightPair (a b c : ZMod 8) : Type :=
  FusionTable.Index b c × FusionTable.Index a (b + c)

/-- Numerical rank of the parity-aligned left row-pair frame. -/
theorem leftPairTotal_eq_sigma (a b c : ZMod 8) :
    ((realSize a b).1 * (realSize (a + b) c).1 +
        (realSize a b).2 * (realSize (a + b) c).2) +
      ((realSize a b).1 * (realSize (a + b) c).2 +
        (realSize a b).2 * (realSize (a + b) c).1) =
      sigma a b c := by
  exact ConnectorTableRankLaws.leftTotal_eq_sigma a b c

/-- Numerical rank of the parity-aligned right row-pair frame. -/
theorem rightPairTotal_eq_sigma (a b c : ZMod 8) :
    ((realSize b c).1 * (realSize a (b + c)).1 +
        (realSize b c).2 * (realSize a (b + c)).2) +
      ((realSize b c).1 * (realSize a (b + c)).2 +
        (realSize b c).2 * (realSize a (b + c)).1) =
      sigma a b c := by
  exact ConnectorTableRankLaws.rightTotal_eq_sigma a b c

/-- Parity-align and flatten a left-associated fusion-row pair. -/
def leftPairEquiv (a b c : ZMod 8) :
    LeftPair a b c ≃ Fin (sigma a b c) :=
  (RMod.ConstructiveRouteFrame.frameEquiv
      (realSize a b).1 (realSize a b).2
      (realSize (a + b) c).1 (realSize (a + b) c).2).trans
    (finCongr (leftPairTotal_eq_sigma a b c))

/-- Parity-align and flatten a right-associated fusion-row pair. -/
def rightPairEquiv (a b c : ZMod 8) :
    RightPair a b c ≃ Fin (sigma a b c) :=
  (RMod.ConstructiveRouteFrame.frameEquiv
      (realSize b c).1 (realSize b c).2
      (realSize a (b + c)).1 (realSize a (b + c)).2).trans
    (finCongr (rightPairTotal_eq_sigma a b c))

/-! ## Flat and pair-indexed coefficient kernels

These are derived views of `forwardCoeff` and `inverseNumeratorCoeff`; no new
coefficient data is selected or computed.
-/

/-- The forward table entry at two flat connector positions. -/
def rawForwardFlatCoeff (a b c : ZMod 8)
    (target source : Fin (sigma a b c)) : Coeff (a + b + c) :=
  fun e =>
    (coeffOf (sigma a b c) (realRepDim (a + b + c).val)
      (forwardCoeff a b c) target source e : Real)

/-- The unscaled inverse-numerator entry at two flat connector positions. -/
def rawInverseNumeratorFlatCoeff (a b c : ZMod 8)
    (target source : Fin (sigma a b c)) : Coeff (a + b + c) :=
  fun e =>
    (coeffOf (sigma a b c) (realRepDim (a + b + c).val)
      (inverseNumeratorCoeff a b c) target source e : Real)

/-- The forward coefficient kernel in its native right-by-left pair frame. -/
def rawForwardPairCoeff (a b c : ZMod 8)
    (target : RightPair a b c) (source : LeftPair a b c) :
    Coeff (a + b + c) :=
  rawForwardFlatCoeff a b c
    (rightPairEquiv a b c target) (leftPairEquiv a b c source)

/-- The inverse-numerator coefficient kernel in its native left-by-right pair
frame. -/
def rawInverseNumeratorPairCoeff (a b c : ZMod 8)
    (target : LeftPair a b c) (source : RightPair a b c) :
    Coeff (a + b + c) :=
  rawInverseNumeratorFlatCoeff a b c
    (leftPairEquiv a b c target) (rightPairEquiv a b c source)

/-! ## The table coefficient label

The list generator uses the natural representative sum modulo eight, whereas
`Coeff` is indexed by the corresponding `ZMod 8` sum.  The next equality is
the only transport between those spellings.
-/

/-- The total `ZMod 8` label has the representative used by the raw table. -/
theorem totalLabel_val (a b c : ZMod 8) :
    (a + b + c).val = (a.val + b.val + c.val) % 8 := by
  rw [ZMod.val_add, ZMod.val_add]
  omega

/-- Forward-then-inverse coefficient identity at the public total label. -/
theorem rawForwardInverseCoeffAtTotalLabel (a b c : ZMod 8)
    (r t : Fin (sigma a b c))
    (e : Fin (realRepDim (a + b + c).val)) :
    convCoeff (realRepMulSign (a + b + c)) (realRepMulIdx (a + b + c))
        (coeffOf (sigma a b c) (realRepDim (a + b + c).val)
          (forwardCoeff a b c))
        (coeffOf (sigma a b c) (realRepDim (a + b + c).val)
          (inverseNumeratorCoeff a b c))
        r t e =
      if r = t ∧ e.val = 0 then (inverseScale a b c : Int) else 0 := by
  unfold realRepMulSign realRepMulIdx
  generalize htotal : (a + b + c).val = total at e ⊢
  have htotal' : total = (a.val + b.val + c.val) % 8 :=
    htotal.symm.trans (totalLabel_val a b c)
  clear htotal
  subst total
  exact rawForwardInverseCoeff a b c r t e

/-- Inverse-then-forward coefficient identity at the public total label. -/
theorem rawInverseForwardCoeffAtTotalLabel (a b c : ZMod 8)
    (r t : Fin (sigma a b c))
    (e : Fin (realRepDim (a + b + c).val)) :
    convCoeff (realRepMulSign (a + b + c)) (realRepMulIdx (a + b + c))
        (coeffOf (sigma a b c) (realRepDim (a + b + c).val)
          (inverseNumeratorCoeff a b c))
        (coeffOf (sigma a b c) (realRepDim (a + b + c).val)
          (forwardCoeff a b c))
        r t e =
      if r = t ∧ e.val = 0 then (inverseScale a b c : Int) else 0 := by
  unfold realRepMulSign realRepMulIdx
  generalize htotal : (a + b + c).val = total at e ⊢
  have htotal' : total = (a.val + b.val + c.val) % 8 :=
    htotal.symm.trans (totalLabel_val a b c)
  clear htotal
  subst total
  exact rawInverseForwardCoeff a b c r t e

/-! ## Flat coefficient-algebra inverse laws

Casting the checked integral convolution to `Real` gives multiplication in
`Coeff`.  Only commutativity of real scalars is used to reorder the sign
factor into the convention of `Coeff.mul`.
-/

private theorem rawForwardInverseFlatSum (a b c : ZMod 8)
    (r t : Fin (sigma a b c)) :
    (∑ middle : Fin (sigma a b c),
      Coeff.mul (a + b + c)
        (rawForwardFlatCoeff a b c r middle)
        (rawInverseNumeratorFlatCoeff a b c middle t)) =
      if r = t then
        Coeff.smul (a + b + c) (inverseScale a b c : Real)
          (Coeff.one (a + b + c))
      else Coeff.zero (a + b + c) := by
  funext e
  have hconvReal :
      (∑ middle : Fin (sigma a b c),
        ∑ i : Fin (realRepDim (a + b + c).val),
          (realRepMulSign (a + b + c) i
              (realRepMulIdx (a + b + c) i e) : Real) *
            (coeffOf (sigma a b c) (realRepDim (a + b + c).val)
              (forwardCoeff a b c) r middle i : Real) *
            (coeffOf (sigma a b c) (realRepDim (a + b + c).val)
              (inverseNumeratorCoeff a b c) middle t
                (realRepMulIdx (a + b + c) i e) : Real)) =
        if r = t ∧ e.val = 0 then (inverseScale a b c : Real) else 0 := by
    have h := congrArg (fun z : Int => (z : Real))
      (rawForwardInverseCoeffAtTotalLabel a b c r t e)
    simpa [convCoeff] using h
  rw [Finset.sum_apply]
  change
    (∑ middle : Fin (sigma a b c),
      ∑ i : Fin (realRepDim (a + b + c).val),
        (coeffOf (sigma a b c) (realRepDim (a + b + c).val)
            (forwardCoeff a b c) r middle i : Real) *
          (coeffOf (sigma a b c) (realRepDim (a + b + c).val)
            (inverseNumeratorCoeff a b c) middle t
              (realRepMulIdx (a + b + c) i e) : Real) *
          (realRepMulSign (a + b + c) i
            (realRepMulIdx (a + b + c) i e) : Real)) = _
  calc
    _ = ∑ middle : Fin (sigma a b c),
        ∑ i : Fin (realRepDim (a + b + c).val),
          (realRepMulSign (a + b + c) i
              (realRepMulIdx (a + b + c) i e) : Real) *
            (coeffOf (sigma a b c) (realRepDim (a + b + c).val)
              (forwardCoeff a b c) r middle i : Real) *
            (coeffOf (sigma a b c) (realRepDim (a + b + c).val)
              (inverseNumeratorCoeff a b c) middle t
                (realRepMulIdx (a + b + c) i e) : Real) := by
          apply Finset.sum_congr rfl
          intro middle _
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = if r = t ∧ e.val = 0 then
          (inverseScale a b c : Real) else 0 := hconvReal
    _ = (if r = t then
          Coeff.smul (a + b + c) (inverseScale a b c : Real)
            (Coeff.one (a + b + c))
        else Coeff.zero (a + b + c)) e := by
          by_cases hrt : r = t <;> by_cases he : e.val = 0 <;>
            simp [hrt, he, Coeff.smul, Coeff.one, Coeff.zero]

private theorem rawInverseForwardFlatSum (a b c : ZMod 8)
    (r t : Fin (sigma a b c)) :
    (∑ middle : Fin (sigma a b c),
      Coeff.mul (a + b + c)
        (rawInverseNumeratorFlatCoeff a b c r middle)
        (rawForwardFlatCoeff a b c middle t)) =
      if r = t then
        Coeff.smul (a + b + c) (inverseScale a b c : Real)
          (Coeff.one (a + b + c))
      else Coeff.zero (a + b + c) := by
  funext e
  have hconvReal :
      (∑ middle : Fin (sigma a b c),
        ∑ i : Fin (realRepDim (a + b + c).val),
          (realRepMulSign (a + b + c) i
              (realRepMulIdx (a + b + c) i e) : Real) *
            (coeffOf (sigma a b c) (realRepDim (a + b + c).val)
              (inverseNumeratorCoeff a b c) r middle i : Real) *
            (coeffOf (sigma a b c) (realRepDim (a + b + c).val)
              (forwardCoeff a b c) middle t
                (realRepMulIdx (a + b + c) i e) : Real)) =
        if r = t ∧ e.val = 0 then (inverseScale a b c : Real) else 0 := by
    have h := congrArg (fun z : Int => (z : Real))
      (rawInverseForwardCoeffAtTotalLabel a b c r t e)
    simpa [convCoeff] using h
  rw [Finset.sum_apply]
  change
    (∑ middle : Fin (sigma a b c),
      ∑ i : Fin (realRepDim (a + b + c).val),
        (coeffOf (sigma a b c) (realRepDim (a + b + c).val)
            (inverseNumeratorCoeff a b c) r middle i : Real) *
          (coeffOf (sigma a b c) (realRepDim (a + b + c).val)
            (forwardCoeff a b c) middle t
              (realRepMulIdx (a + b + c) i e) : Real) *
          (realRepMulSign (a + b + c) i
            (realRepMulIdx (a + b + c) i e) : Real)) = _
  calc
    _ = ∑ middle : Fin (sigma a b c),
        ∑ i : Fin (realRepDim (a + b + c).val),
          (realRepMulSign (a + b + c) i
              (realRepMulIdx (a + b + c) i e) : Real) *
            (coeffOf (sigma a b c) (realRepDim (a + b + c).val)
              (inverseNumeratorCoeff a b c) r middle i : Real) *
            (coeffOf (sigma a b c) (realRepDim (a + b + c).val)
              (forwardCoeff a b c) middle t
                (realRepMulIdx (a + b + c) i e) : Real) := by
          apply Finset.sum_congr rfl
          intro middle _
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = if r = t ∧ e.val = 0 then
          (inverseScale a b c : Real) else 0 := hconvReal
    _ = (if r = t then
          Coeff.smul (a + b + c) (inverseScale a b c : Real)
            (Coeff.one (a + b + c))
        else Coeff.zero (a + b + c)) e := by
          by_cases hrt : r = t <;> by_cases he : e.val = 0 <;>
            simp [hrt, he, Coeff.smul, Coeff.one, Coeff.zero]

/-! ## Native pair-frame Kronecker identities

Reindexing the middle flat row by the corresponding route-pair equivalence
gives the exact kernels consumed by the raw forward and reverse maps.
-/

/-- Forward followed by the unscaled inverse numerator is `lambda` times the
identity kernel on the right-associated raw route. -/
theorem rawForwardInversePairSum (a b c : ZMod 8)
    (target source : RightPair a b c) :
    (∑ middle : LeftPair a b c,
      Coeff.mul (a + b + c)
        (rawForwardPairCoeff a b c target middle)
        (rawInverseNumeratorPairCoeff a b c middle source)) =
      if target = source then
        Coeff.smul (a + b + c) (inverseScale a b c : Real)
          (Coeff.one (a + b + c))
      else Coeff.zero (a + b + c) := by
  let F : Fin (sigma a b c) → Coeff (a + b + c) := fun middle =>
    Coeff.mul (a + b + c)
      (rawForwardFlatCoeff a b c (rightPairEquiv a b c target) middle)
      (rawInverseNumeratorFlatCoeff a b c middle
        (rightPairEquiv a b c source))
  calc
    _ = ∑ middle : Fin (sigma a b c), F middle := by
      simpa [F, rawForwardPairCoeff, rawInverseNumeratorPairCoeff] using
        (Equiv.sum_comp (leftPairEquiv a b c) F)
    _ = if rightPairEquiv a b c target = rightPairEquiv a b c source then
          Coeff.smul (a + b + c) (inverseScale a b c : Real)
            (Coeff.one (a + b + c))
        else Coeff.zero (a + b + c) :=
      rawForwardInverseFlatSum a b c
        (rightPairEquiv a b c target) (rightPairEquiv a b c source)
    _ = _ := by
      by_cases h : target = source
      · subst source
        simp
      · have hmap :
            rightPairEquiv a b c target ≠ rightPairEquiv a b c source :=
          fun heq => h ((rightPairEquiv a b c).injective heq)
        simp [h, hmap]

/-- The unscaled inverse numerator followed by the forward kernel is
`lambda` times the identity kernel on the left-associated raw route. -/
theorem rawInverseForwardPairSum (a b c : ZMod 8)
    (target source : LeftPair a b c) :
    (∑ middle : RightPair a b c,
      Coeff.mul (a + b + c)
        (rawInverseNumeratorPairCoeff a b c target middle)
        (rawForwardPairCoeff a b c middle source)) =
      if target = source then
        Coeff.smul (a + b + c) (inverseScale a b c : Real)
          (Coeff.one (a + b + c))
      else Coeff.zero (a + b + c) := by
  let F : Fin (sigma a b c) → Coeff (a + b + c) := fun middle =>
    Coeff.mul (a + b + c)
      (rawInverseNumeratorFlatCoeff a b c (leftPairEquiv a b c target) middle)
      (rawForwardFlatCoeff a b c middle (leftPairEquiv a b c source))
  calc
    _ = ∑ middle : Fin (sigma a b c), F middle := by
      simpa [F, rawForwardPairCoeff, rawInverseNumeratorPairCoeff] using
        (Equiv.sum_comp (rightPairEquiv a b c) F)
    _ = if leftPairEquiv a b c target = leftPairEquiv a b c source then
          Coeff.smul (a + b + c) (inverseScale a b c : Real)
            (Coeff.one (a + b + c))
        else Coeff.zero (a + b + c) :=
      rawInverseForwardFlatSum a b c
        (leftPairEquiv a b c target) (leftPairEquiv a b c source)
    _ = _ := by
      by_cases h : target = source
      · subst source
        simp
      · have hmap :
            leftPairEquiv a b c target ≠ leftPairEquiv a b c source :=
          fun heq => h ((leftPairEquiv a b c).injective heq)
        simp [h, hmap]

end ConnectorTableLaws
end RModCoordinate
end Superfusion
