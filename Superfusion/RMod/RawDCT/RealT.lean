import Superfusion.GaugeChi.RealGaugeTables
import Superfusion.RMod.Constructive.ConnectorTableData
import Superfusion.RMod.Constructive.ConnectorTableRouteInverseLaws
import Superfusion.RMod.Constructive.RawSemanticConnectorMem
import Superfusion.RMod.Constructive.RouteFrame
import Superfusion.RMod.RawDCT.RealC
import Superfusion.RMod.RawDCT.T

/-!
# Concrete computable raw real connector

This file constructs the concrete `TData` over `realDData` and `realCData`.
Both ternary routes are actual finite coordinate bimodules.  The forward map
is read directly from `ConstructiveConnectorTable.forwardCoeff`; the reverse
map is the recorded conjugate-transpose numerator scaled by an exact rational
number before casting to `ℝ`.

No semantic connector, selected inverse, `ν`, `β`, or shifted kernel occurs in
the data layer.  Proof-only bridges used to establish `TLaws` follow the data
definitions below.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT

open RModCoordinate
open RModCoordinate.FusionTable
open RMod.ConstructiveConnectorTable
open RMod.ConstructiveRouteFrame

/-! ## Concrete route carriers -/

abbrev RealLeftRouteCarrier (a b c : ZMod 8) : Type :=
  LeftRouteCoordinates realCData a b c

abbrev RealRightRouteCarrier (a b c : ZMod 8) : Type :=
  RightRouteCoordinates realCData a b c

def realLeftRouteZero (a b c : ZMod 8) : RealLeftRouteCarrier a b c :=
  fun _ _ => Coeff.zero (a + b + c)

def realLeftRouteAdd (a b c : ZMod 8)
    (x y : RealLeftRouteCarrier a b c) : RealLeftRouteCarrier a b c :=
  fun r s => Coeff.add (a + b + c) (x r s) (y r s)

def realLeftRouteNeg (a b c : ZMod 8)
    (x : RealLeftRouteCarrier a b c) : RealLeftRouteCarrier a b c :=
  fun r s => Coeff.neg (a + b + c) (x r s)

def realLeftRouteSmul (a b c : ZMod 8) (q : ℝ)
    (x : RealLeftRouteCarrier a b c) : RealLeftRouteCarrier a b c :=
  fun r s => Coeff.smul (a + b + c) q (x r s)

def realLeftRouteComponent (a b c : ZMod 8) (i : ZMod 2)
    (x : RealLeftRouteCarrier a b c) : RealLeftRouteCarrier a b c :=
  fun r s => Coeff.component (a + b + c)
    (i + realCData.rowParity a b r + realCData.rowParity (a + b) c s)
    (x r s)

def realLeftRouteLeftPure (a b c : ZMod 8)
    (x : Coeff a) (y : Coeff b) (z : Coeff c)
    (m : RealLeftRouteCarrier a b c) : RealLeftRouteCarrier a b c :=
  fun targetAB targetABC =>
    CData.rawFinSum (realDData.algebra (a + b + c)) fun sourceAB =>
      CData.rawFinSum (realDData.algebra (a + b + c)) fun sourceABC =>
        Coeff.mul (a + b + c)
          (leftRouteCoeff realCData a b c targetAB targetABC
            sourceAB sourceABC x y z)
          (m sourceAB sourceABC)

def realLeftRouteRight (a b c : ZMod 8)
    (m : RealLeftRouteCarrier a b c) (q : Coeff (a + b + c)) :
    RealLeftRouteCarrier a b c :=
  fun r s => Coeff.mul (a + b + c) (m r s) q

def realRightRouteZero (a b c : ZMod 8) : RealRightRouteCarrier a b c :=
  fun _ _ => Coeff.zero (a + b + c)

def realRightRouteAdd (a b c : ZMod 8)
    (x y : RealRightRouteCarrier a b c) : RealRightRouteCarrier a b c :=
  fun r s => Coeff.add (a + b + c) (x r s) (y r s)

def realRightRouteNeg (a b c : ZMod 8)
    (x : RealRightRouteCarrier a b c) : RealRightRouteCarrier a b c :=
  fun r s => Coeff.neg (a + b + c) (x r s)

def realRightRouteSmul (a b c : ZMod 8) (q : ℝ)
    (x : RealRightRouteCarrier a b c) : RealRightRouteCarrier a b c :=
  fun r s => Coeff.smul (a + b + c) q (x r s)

def realRightRouteComponent (a b c : ZMod 8) (i : ZMod 2)
    (x : RealRightRouteCarrier a b c) : RealRightRouteCarrier a b c :=
  fun r s => Coeff.component (a + b + c)
    (i + realCData.rowParity b c r + realCData.rowParity a (b + c) s)
    (x r s)

def realRightRouteLeftPure (a b c : ZMod 8)
    (x : Coeff a) (y : Coeff b) (z : Coeff c)
    (m : RealRightRouteCarrier a b c) : RealRightRouteCarrier a b c :=
  fun targetBC targetABC =>
    CData.rawFinSum (realDData.algebra (a + b + c)) fun sourceBC =>
      CData.rawFinSum (realDData.algebra (a + b + c)) fun sourceABC =>
        Coeff.mul (a + b + c)
          (rightRouteCoeff realCData a b c targetBC targetABC
            sourceBC sourceABC x y z)
          (m sourceBC sourceABC)

def realRightRouteRight (a b c : ZMod 8)
    (m : RealRightRouteCarrier a b c) (q : Coeff (a + b + c)) :
    RealRightRouteCarrier a b c :=
  fun r s => Coeff.mul (a + b + c) (m r s) q

/-- Executable left-associated ternary route. -/
def realLeftRouteData : TripleRouteData realDData where
  carrier := RealLeftRouteCarrier
  zero := realLeftRouteZero
  add := realLeftRouteAdd
  neg := realLeftRouteNeg
  smul := realLeftRouteSmul
  component := realLeftRouteComponent
  leftPure := realLeftRouteLeftPure
  right := realLeftRouteRight

/-- Executable right-associated ternary route. -/
def realRightRouteData : TripleRouteData realDData where
  carrier := RealRightRouteCarrier
  zero := realRightRouteZero
  add := realRightRouteAdd
  neg := realRightRouteNeg
  smul := realRightRouteSmul
  component := realRightRouteComponent
  leftPure := realRightRouteLeftPure
  right := realRightRouteRight

/-! ## Connector frame positions and coefficients -/

/-- Position of a pair of binary fusion rows in the parity-aligned left
connector frame. -/
def realTLeftPosition (a b c : ZMod 8)
    (r : FusionTable.Index a b) (s : FusionTable.Index (a + b) c) : ℕ :=
  (RMod.ConstructiveRouteFrame.frameEquiv
    (realSize a b).1 (realSize a b).2
    (realSize (a + b) c).1 (realSize (a + b) c).2 (r, s)).val

/-- Position of a pair of binary fusion rows in the parity-aligned right
connector frame. -/
def realTRightPosition (a b c : ZMod 8)
    (r : FusionTable.Index b c) (s : FusionTable.Index a (b + c)) : ℕ :=
  (RMod.ConstructiveRouteFrame.frameEquiv
    (realSize b c).1 (realSize b c).2
    (realSize a (b + c)).1 (realSize a (b + c)).2 (r, s)).val

/-- One coefficient-algebra entry of the frozen forward connector. -/
def realTForwardEntry (a b c : ZMod 8)
    (targetBC : FusionTable.Index b c)
    (targetABC : FusionTable.Index a (b + c))
    (sourceAB : FusionTable.Index a b)
    (sourceABC : FusionTable.Index (a + b) c) : Coeff (a + b + c) :=
  fun e =>
    (coeffGet (forwardCoeff a b c)
      (realTRightPosition a b c targetBC targetABC)
      (realTLeftPosition a b c sourceAB sourceABC) e.val : ℝ)

/-- Exact reciprocal of the positive integral connector norm.  Division is
performed in `ℚ`, before the result is cast to `ℝ`. -/
def realTInverseScale (a b c : ZMod 8) : ℝ :=
  ((1 / (inverseScale a b c : ℚ) : ℚ) : ℝ)

/-- One coefficient-algebra entry of the explicit reverse connector. -/
def realTInverseEntry (a b c : ZMod 8)
    (targetAB : realCData.Index a b)
    (targetABC : realCData.Index (a + b) c)
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c)) : Coeff (a + b + c) :=
  fun e => realTInverseScale a b c *
    (coeffGet (inverseNumeratorCoeff a b c)
      (realTLeftPosition a b c targetAB targetABC)
      (realTRightPosition a b c sourceBC sourceABC) e.val : ℝ)

/-! ## Explicit forward and reverse maps -/

def realTHom (a b c : ZMod 8) (m : RealLeftRouteCarrier a b c) :
    RealRightRouteCarrier a b c :=
  fun targetBC targetABC =>
    CData.rawFinSum (realDData.algebra (a + b + c)) fun sourceAB =>
      CData.rawFinSum (realDData.algebra (a + b + c)) fun sourceABC =>
        Coeff.mul (a + b + c)
          (realTForwardEntry a b c targetBC targetABC sourceAB sourceABC)
          (m sourceAB sourceABC)

def realTInv (a b c : ZMod 8) (m : RealRightRouteCarrier a b c) :
    RealLeftRouteCarrier a b c :=
  fun targetAB targetABC =>
    CData.rawFinSum (realDData.algebra (a + b + c)) fun sourceBC =>
      CData.rawFinSum (realDData.algebra (a + b + c)) fun sourceABC =>
        Coeff.mul (a + b + c)
          (realTInverseEntry a b c targetAB targetABC sourceBC sourceABC)
          (m sourceBC sourceABC)

/-- Raw parity, with additive labels converted only to the multiplicative
indexing convention of the frozen table. -/
def realTParity (a b c : ZMod 8) : ZMod 2 :=
  GaugeChi.realLeanParityTable
    (Multiplicative.ofAdd a) (Multiplicative.ofAdd b) (Multiplicative.ofAdd c)

/-- Complete executable raw real connector data. -/
def realTData : TData realDData realCData where
  leftRoute := realLeftRouteData
  rightRoute := realRightRouteData
  leftToCoord := fun _ _ _ x => x
  leftOfCoord := fun _ _ _ x => x
  rightToCoord := fun _ _ _ x => x
  rightOfCoord := fun _ _ _ x => x
  parity := realTParity
  hom := realTHom
  inv := realTInv

/-! ## Laws of the two concrete routes -/

/- The route action is a finite matrix action.  These bridges expose its two
stored `rawFinSum`s as ordinary finite sums, so the already-proved coordinate
algebra laws can be applied without any evaluation of the frozen tables. -/

private theorem realTRawFinSum_eq_sum {a : ZMod 8} {n : ℕ}
    (f : Fin n → Coeff a) :
    CData.rawFinSum (realDData.algebra a) f = ∑ r, f r := by
  change (List.ofFn f).sum = ∑ r, f r
  exact List.sum_ofFn

private theorem realTCoeff_mul_sum {I : Type*} [Fintype I] (a : ZMod 8)
    (x : Coeff a) (f : I → Coeff a) :
    Coeff.mul a x (∑ r, f r) = ∑ r, Coeff.mul a x (f r) := by
  apply (Coeff.semantic a).injective
  simpa only [map_sum, Coeff.semantic_mul] using
    (Finset.mul_sum (s := Finset.univ) (fun r => Coeff.semantic a (f r))
      (Coeff.semantic a x))

private theorem realTCoeff_sum_mul {I : Type*} [Fintype I] (a : ZMod 8)
    (f : I → Coeff a) (x : Coeff a) :
    Coeff.mul a (∑ r, f r) x = ∑ r, Coeff.mul a (f r) x := by
  apply (Coeff.semantic a).injective
  simpa only [map_sum, Coeff.semantic_mul] using
    (Finset.sum_mul (s := Finset.univ) (fun r => Coeff.semantic a (f r))
      (Coeff.semantic a x))

private theorem realTCoeff_smul_sum {I : Type*} [Fintype I] (a : ZMod 8)
    (q : ℝ) (f : I → Coeff a) :
    Coeff.smul a q (∑ r, f r) = ∑ r, Coeff.smul a q (f r) := by
  ext g
  simp only [Coeff.smul, Finset.sum_apply]
  exact Finset.mul_sum (s := Finset.univ) (fun r => f r g) q

private theorem realTCoeff_sum_zero {I : Type*} [Fintype I] (a : ZMod 8) :
    (∑ _ : I, Coeff.zero a) = Coeff.zero a := by
  ext g
  simp [Coeff.zero]

private theorem realTCoeff_sum_memGrade {I : Type*} [Fintype I]
    (a : ZMod 8) (i : ZMod 2) (f : I → Coeff a)
    (hf : ∀ r, Coeff.MemGrade a i (f r)) :
    Coeff.MemGrade a i (∑ r, f r) := by
  intro g hg
  simp only [Finset.sum_apply]
  exact Finset.sum_eq_zero fun r _ => hf r g hg

/- Transport across `a + (b + c) = a + b + c` is computationally a cast.
The following laws are proved once by equality induction and are used only
for the right-associated route. -/

private def realCoeffCast {u v : ZMod 8} (h : u = v) : Coeff u → Coeff v :=
  cast (congrArg Coeff h)

private theorem realCoeffCast_apply {u v : ZMod 8} (h : u = v)
    (x : Coeff u) (g : Fin (realRepDim v.val)) :
    realCoeffCast h x g =
      x ((finCongr (congrArg (fun z : ZMod 8 => realRepDim z.val) h)).symm g) := by
  subst v
  rfl

private theorem realCoeffCast_zero {u v : ZMod 8} (h : u = v) :
    realCoeffCast h (Coeff.zero u) = Coeff.zero v := by
  subst v
  rfl

private theorem realCoeffCast_one {u v : ZMod 8} (h : u = v) :
    realCoeffCast h (Coeff.one u) = Coeff.one v := by
  subst v
  rfl

private theorem realCoeffCast_add {u v : ZMod 8} (h : u = v)
    (x y : Coeff u) :
    realCoeffCast h (Coeff.add u x y) =
      Coeff.add v (realCoeffCast h x) (realCoeffCast h y) := by
  subst v
  rfl

private theorem realCoeffCast_smul {u v : ZMod 8} (h : u = v)
    (q : ℝ) (x : Coeff u) :
    realCoeffCast h (Coeff.smul u q x) =
      Coeff.smul v q (realCoeffCast h x) := by
  subst v
  rfl

private theorem realCoeffCast_mul {u v : ZMod 8} (h : u = v)
    (x y : Coeff u) :
    realCoeffCast h (Coeff.mul u x y) =
      Coeff.mul v (realCoeffCast h x) (realCoeffCast h y) := by
  subst v
  rfl

private theorem realCoeffCast_sum {u v : ZMod 8} (h : u = v)
    {I : Type*} [Fintype I] (f : I → Coeff u) :
    realCoeffCast h (∑ r, f r) = ∑ r, realCoeffCast h (f r) := by
  subst v
  rfl

private theorem realCoeffCast_memGrade {u v : ZMod 8} (h : u = v)
    (i : ZMod 2) {x : Coeff u} (hx : Coeff.MemGrade u i x) :
    Coeff.MemGrade v i (realCoeffCast h x) := by
  subst v
  exact hx

private theorem realRouteCastAssoc_eq (a b c : ZMod 8)
    (x : Coeff (a + (b + c))) :
    routeCastAssoc realDData a b c x =
      realCoeffCast (_root_.add_assoc a b c).symm x :=
  rfl

/- The public parity sign is a character of the additive parity group. -/

private theorem realTZMod2_one_add_one : (1 : ZMod 2) + 1 = 0 := rfl

private theorem realTParitySign_add (i j : ZMod 2) :
    paritySign (i + j) = paritySign i * paritySign j := by
  rcases zmod2_cases i with rfl | rfl <;>
    rcases zmod2_cases j with rfl | rfl <;>
      simp [paritySign, realTZMod2_one_add_one]

private theorem realTIntSgnCast_eq_paritySign (i : ZMod 2) :
    ((((sgn i : ℤˣ) : ℤ) : ℝ)) = paritySign i := by
  rcases zmod2_cases i with rfl | rfl <;> simp [paritySign]

private theorem realTParitySign_cancel_right (p q i : ZMod 2) :
    paritySign ((p + q) * i) * paritySign (q * i) = paritySign (p * i) := by
  rcases zmod2_cases p with rfl | rfl <;>
    rcases zmod2_cases q with rfl | rfl <;>
      rcases zmod2_cases i with rfl | rfl <;>
        simp [paritySign, realTZMod2_one_add_one]

private theorem realTParitySign_cancel_left (p q i : ZMod 2) :
    paritySign ((p + q) * i) * paritySign (p * i) = paritySign (q * i) := by
  rcases zmod2_cases p with rfl | rfl <;>
    rcases zmod2_cases q with rfl | rfl <;>
      rcases zmod2_cases i with rfl | rfl <;>
        simp [paritySign, realTZMod2_one_add_one]

private theorem realTParitySign_route_left
    (i j p q : ZMod 2) :
    paritySign (i * (j + p + q)) * paritySign ((p + q) * i) =
      paritySign (i * j) := by
  rcases zmod2_cases i with rfl | rfl <;>
    rcases zmod2_cases j with rfl | rfl <;>
      rcases zmod2_cases p with rfl | rfl <;>
        rcases zmod2_cases q with rfl | rfl <;>
          simp [paritySign, realTZMod2_one_add_one]

private theorem realTParitySign_route_right
    (i j p q : ZMod 2) :
    paritySign ((i + p + q) * j) * paritySign ((p + q) * j) =
      paritySign (i * j) := by
  rcases zmod2_cases i with rfl | rfl <;>
    rcases zmod2_cases j with rfl | rfl <;>
      rcases zmod2_cases p with rfl | rfl <;>
        rcases zmod2_cases q with rfl | rfl <;>
          simp [paritySign, realTZMod2_one_add_one]

private theorem realTParitySign_left_total (i j k l : ZMod 2) :
    paritySign (k * (j + l)) * paritySign (i * j) =
      paritySign (i * j + k * (j + l)) := by
  rw [realTParitySign_add]
  ring

private theorem realTParitySign_right_total (i j k l : ZMod 2) :
    paritySign ((j + k) * i) * paritySign (k * l) =
      paritySign (j * i + k * (i + l)) := by
  rcases zmod2_cases i with rfl | rfl <;>
    rcases zmod2_cases j with rfl | rfl <;>
      rcases zmod2_cases k with rfl | rfl <;>
        rcases zmod2_cases l with rfl | rfl <;>
          simp [paritySign, realTZMod2_one_add_one]

/- `routeRowTwist` is the parity character on each homogeneous coordinate.
This makes its multiplicativity and the two row-sign cancellation identities
independent of the concrete fusion tables. -/

private theorem realRouteRowTwist_apply (a : ZMod 8) (p : ZMod 2)
    (x : Coeff a) (g : Fin (realRepDim a.val)) :
    routeRowTwist realDData a p x g =
      paritySign (p * realRepBasisParity a g) * x g := by
  unfold routeRowTwist realDData coordinateSuperAlgebraData
  simp only [Coeff.add_apply, Coeff.component_apply, Coeff.smul_apply]
  generalize realRepBasisParity a g = i
  rcases zmod2_cases p with rfl | rfl <;>
    rcases zmod2_cases i with rfl | rfl <;> norm_num [paritySign]

private theorem realRouteRowTwist_of_memGrade (a : ZMod 8)
    (p i : ZMod 2) (x : Coeff a) (hx : Coeff.MemGrade a i x) :
    routeRowTwist realDData a p x =
      Coeff.smul a (paritySign (p * i)) x := by
  apply Coeff.ext
  intro g
  rw [realRouteRowTwist_apply]
  simp only [Coeff.smul_apply]
  by_cases hg : realRepBasisParity a g = i
  · rw [hg]
  · rw [hx g hg]
    ring

private theorem realRouteRowTwist_zero (a : ZMod 8) (p : ZMod 2) :
    routeRowTwist realDData a p (Coeff.zero a) = Coeff.zero a := by
  apply Coeff.ext
  intro g
  simp [realRouteRowTwist_apply]

private theorem realRouteRowTwist_add (a : ZMod 8) (p : ZMod 2)
    (x y : Coeff a) :
    routeRowTwist realDData a p (Coeff.add a x y) =
      Coeff.add a (routeRowTwist realDData a p x)
        (routeRowTwist realDData a p y) := by
  apply Coeff.ext
  intro g
  simp only [realRouteRowTwist_apply, Coeff.add_apply]
  ring

private theorem realRouteRowTwist_smul (a : ZMod 8) (p : ZMod 2)
    (q : ℝ) (x : Coeff a) :
    routeRowTwist realDData a p (Coeff.smul a q x) =
      Coeff.smul a q (routeRowTwist realDData a p x) := by
  apply Coeff.ext
  intro g
  simp only [realRouteRowTwist_apply, Coeff.smul_apply]
  ring

private theorem realRouteRowTwist_one (a : ZMod 8) (p : ZMod 2) :
    routeRowTwist realDData a p (Coeff.one a) = Coeff.one a := by
  rw [realRouteRowTwist_of_memGrade a p 0 (Coeff.one a) (Coeff.memGrade_one a)]
  simpa [paritySign] using Coeff.one_smul a (Coeff.one a)

private theorem realRouteRowTwist_mul (a : ZMod 8) (p : ZMod 2)
    (x y : Coeff a) :
    routeRowTwist realDData a p (Coeff.mul a x y) =
      Coeff.mul a (routeRowTwist realDData a p x)
        (routeRowTwist realDData a p y) := by
  apply Coeff.ext
  intro k
  rw [realRouteRowTwist_apply]
  simp only [Coeff.mul, realRouteRowTwist_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hparity :
      realRepBasisParity a k =
        realRepBasisParity a i +
          realRepBasisParity a (realRepMulIdx a i k) := by
    simpa [realRepMulIdx_involutive] using
      (Coeff.basisParity_mulIdx a i (realRepMulIdx a i k))
  rw [hparity, mul_add, realTParitySign_add]
  ring

private theorem realTCoeff_twist_scalar_left (a : ZMod 8)
    (p q i : ZMod 2) (x w : Coeff a) :
    Coeff.smul a (paritySign (p * i)) (Coeff.mul a x w) =
      Coeff.smul a (paritySign ((p + q) * i))
        (Coeff.mul a (Coeff.smul a (paritySign (q * i)) x) w) := by
  rw [Coeff.smul_mul, ← Coeff.mul_smul, realTParitySign_cancel_right]

private theorem realTCoeff_twist_scalar_right (a : ZMod 8)
    (p q i : ZMod 2) (w y : Coeff a) :
    Coeff.smul a (paritySign (q * i)) (Coeff.mul a w y) =
      Coeff.smul a (paritySign ((p + q) * i))
        (Coeff.mul a w (Coeff.smul a (paritySign (p * i)) y)) := by
  rw [Coeff.mul_smul_right, ← Coeff.mul_smul,
    realTParitySign_cancel_left]

private theorem realRouteRowTwist_mul_left (a : ZMod 8)
    (p q i : ZMod 2) (x y : Coeff a) (hx : Coeff.MemGrade a i x) :
    Coeff.mul a (routeRowTwist realDData a p x)
        (routeRowTwist realDData a q y) =
      Coeff.smul a (paritySign ((p + q) * i))
        (routeRowTwist realDData a q (Coeff.mul a x y)) := by
  rw [realRouteRowTwist_of_memGrade a p i x hx,
    realRouteRowTwist_mul,
    realRouteRowTwist_of_memGrade a q i x hx]
  rw [Coeff.smul_mul a (paritySign (p * i)) x
    (show Coeff a from routeRowTwist realDData a q y)]
  exact realTCoeff_twist_scalar_left a p q i x
    (show Coeff a from routeRowTwist realDData a q y)

private theorem realRouteRowTwist_mul_right (a : ZMod 8)
    (p q i : ZMod 2) (x y : Coeff a) (hy : Coeff.MemGrade a i y) :
    Coeff.mul a (routeRowTwist realDData a p x)
        (routeRowTwist realDData a q y) =
      Coeff.smul a (paritySign ((p + q) * i))
        (routeRowTwist realDData a p (Coeff.mul a x y)) := by
  rw [realRouteRowTwist_of_memGrade a q i y hy,
    realRouteRowTwist_mul,
    realRouteRowTwist_of_memGrade a p i y hy]
  rw [Coeff.mul_smul_right a (paritySign (q * i))
    (show Coeff a from routeRowTwist realDData a p x) y]
  exact realTCoeff_twist_scalar_right a p q i
    (show Coeff a from routeRowTwist realDData a p x) y

/-! ### Binary coefficient consequences used by both routes -/

private theorem fusionCoefficient_sum_left {I : Type*} [Fintype I]
    (a b : ZMod 8) (target source : FusionTable.Index a b)
    (f : I → Coeff a) (y : Coeff b) :
    fusionCoefficient a b target source (∑ r, f r) y =
      ∑ r, fusionCoefficient a b target source (f r) y := by
  classical
  let s : Finset I := Finset.univ
  change fusionCoefficient a b target source (∑ r ∈ s, f r) y =
    ∑ r ∈ s, fusionCoefficient a b target source (f r) y
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      change fusionCoefficient a b target source (Coeff.zero a) y =
        Coeff.zero (a + b)
      exact FusionTableLaws.fusionCoefficient_zero_left a b target source y
  | @insert r s hr ih =>
      rw [Finset.sum_insert hr, Finset.sum_insert hr]
      change fusionCoefficient a b target source
          (Coeff.add a (f r) (∑ x ∈ s, f x)) y =
        Coeff.add (a + b) (fusionCoefficient a b target source (f r) y)
          (∑ x ∈ s, fusionCoefficient a b target source (f x) y)
      rw [FusionTableLaws.fusionCoefficient_add_left, ih]

private theorem fusionCoefficient_sum_right {I : Type*} [Fintype I]
    (a b : ZMod 8) (target source : FusionTable.Index a b)
    (x : Coeff a) (f : I → Coeff b) :
    fusionCoefficient a b target source x (∑ r, f r) =
      ∑ r, fusionCoefficient a b target source x (f r) := by
  classical
  let s : Finset I := Finset.univ
  change fusionCoefficient a b target source x (∑ r ∈ s, f r) =
    ∑ r ∈ s, fusionCoefficient a b target source x (f r)
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      change fusionCoefficient a b target source x (Coeff.zero b) =
        Coeff.zero (a + b)
      exact FusionTableLaws.fusionCoefficient_zero_right a b target source x
  | @insert r s hr ih =>
      rw [Finset.sum_insert hr, Finset.sum_insert hr]
      change fusionCoefficient a b target source x
          (Coeff.add b (f r) (∑ y ∈ s, f y)) =
        Coeff.add (a + b) (fusionCoefficient a b target source x (f r))
          (∑ y ∈ s, fusionCoefficient a b target source x (f y))
      rw [FusionTableLaws.fusionCoefficient_add_right, ih]

private theorem fusionCoefficient_mul_parity (a b : ZMod 8) (i j : ZMod 2)
    (target source : FusionTable.Index a b)
    (x x' : Coeff a) (y y' : Coeff b)
    (hy : Coeff.MemGrade b j y) (hx' : Coeff.MemGrade a i x') :
    (∑ middle : FusionTable.Index a b,
        Coeff.mul (a + b)
          (fusionCoefficient a b target middle x y)
          (fusionCoefficient a b middle source x' y')) =
      Coeff.smul (a + b) (paritySign (j * i))
        (fusionCoefficient a b target source
          (Coeff.mul a x x') (Coeff.mul b y y')) := by
  simpa only [realTIntSgnCast_eq_paritySign] using
    (FusionTableLaws.fusionCoefficient_mul a b i j target source
      (x := x) (x' := x') (y := y) (y' := y') hy hx')

/-! ### Left-associated route coefficient laws -/

private theorem leftRouteCoeff_eq_fusionCoefficient (a b c : ZMod 8)
    (targetAB : realCData.Index a b)
    (targetABC : realCData.Index (a + b) c)
    (sourceAB : realCData.Index a b)
    (sourceABC : realCData.Index (a + b) c)
    (x : Coeff a) (y : Coeff b) (z : Coeff c) :
    leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC x y z =
      fusionCoefficient (a + b) c targetABC sourceABC
        (fusionCoefficient a b targetAB sourceAB x y)
        (routeRowTwist realDData c (indexParity a b sourceAB) z) :=
  rfl

private theorem leftRouteCoeff_zero_first (a b c : ZMod 8)
    (targetAB : realCData.Index a b)
    (targetABC : realCData.Index (a + b) c)
    (sourceAB : realCData.Index a b)
    (sourceABC : realCData.Index (a + b) c)
    (y : Coeff b) (z : Coeff c) :
    leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
        (Coeff.zero a) y z = Coeff.zero (a + b + c) := by
  rw [leftRouteCoeff_eq_fusionCoefficient]
  rw [FusionTableLaws.fusionCoefficient_zero_left,
    FusionTableLaws.fusionCoefficient_zero_left]

private theorem leftRouteCoeff_zero_second (a b c : ZMod 8)
    (targetAB : realCData.Index a b)
    (targetABC : realCData.Index (a + b) c)
    (sourceAB : realCData.Index a b)
    (sourceABC : realCData.Index (a + b) c)
    (x : Coeff a) (z : Coeff c) :
    leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
        x (Coeff.zero b) z = Coeff.zero (a + b + c) := by
  rw [leftRouteCoeff_eq_fusionCoefficient]
  rw [FusionTableLaws.fusionCoefficient_zero_right,
    FusionTableLaws.fusionCoefficient_zero_left]

private theorem leftRouteCoeff_zero_third (a b c : ZMod 8)
    (targetAB : realCData.Index a b)
    (targetABC : realCData.Index (a + b) c)
    (sourceAB : realCData.Index a b)
    (sourceABC : realCData.Index (a + b) c)
    (x : Coeff a) (y : Coeff b) :
    leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
        x y (Coeff.zero c) = Coeff.zero (a + b + c) := by
  rw [leftRouteCoeff_eq_fusionCoefficient]
  rw [realRouteRowTwist_zero,
    FusionTableLaws.fusionCoefficient_zero_right]

private theorem leftRouteCoeff_add_first (a b c : ZMod 8)
    (targetAB : realCData.Index a b)
    (targetABC : realCData.Index (a + b) c)
    (sourceAB : realCData.Index a b)
    (sourceABC : realCData.Index (a + b) c)
    (x x' : Coeff a) (y : Coeff b) (z : Coeff c) :
    leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
        (Coeff.add a x x') y z =
      Coeff.add (a + b + c)
        (leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
          x y z)
        (leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
          x' y z) := by
  simp_rw [leftRouteCoeff_eq_fusionCoefficient]
  rw [FusionTableLaws.fusionCoefficient_add_left,
    FusionTableLaws.fusionCoefficient_add_left]

private theorem leftRouteCoeff_add_second (a b c : ZMod 8)
    (targetAB : realCData.Index a b)
    (targetABC : realCData.Index (a + b) c)
    (sourceAB : realCData.Index a b)
    (sourceABC : realCData.Index (a + b) c)
    (x : Coeff a) (y y' : Coeff b) (z : Coeff c) :
    leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
        x (Coeff.add b y y') z =
      Coeff.add (a + b + c)
        (leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
          x y z)
        (leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
          x y' z) := by
  simp_rw [leftRouteCoeff_eq_fusionCoefficient]
  rw [FusionTableLaws.fusionCoefficient_add_right,
    FusionTableLaws.fusionCoefficient_add_left]

private theorem leftRouteCoeff_add_third (a b c : ZMod 8)
    (targetAB : realCData.Index a b)
    (targetABC : realCData.Index (a + b) c)
    (sourceAB : realCData.Index a b)
    (sourceABC : realCData.Index (a + b) c)
    (x : Coeff a) (y : Coeff b) (z z' : Coeff c) :
    leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
        x y (Coeff.add c z z') =
      Coeff.add (a + b + c)
        (leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
          x y z)
        (leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
          x y z') := by
  simp_rw [leftRouteCoeff_eq_fusionCoefficient]
  rw [realRouteRowTwist_add,
    FusionTableLaws.fusionCoefficient_add_right]

private theorem leftRouteCoeff_smul_first (a b c : ZMod 8)
    (targetAB : realCData.Index a b)
    (targetABC : realCData.Index (a + b) c)
    (sourceAB : realCData.Index a b)
    (sourceABC : realCData.Index (a + b) c)
    (q : ℝ) (x : Coeff a) (y : Coeff b) (z : Coeff c) :
    leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
        (Coeff.smul a q x) y z =
      Coeff.smul (a + b + c) q
        (leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
          x y z) := by
  simp_rw [leftRouteCoeff_eq_fusionCoefficient]
  rw [FusionTableLaws.fusionCoefficient_smul_left,
    FusionTableLaws.fusionCoefficient_smul_left]

private theorem leftRouteCoeff_smul_second (a b c : ZMod 8)
    (targetAB : realCData.Index a b)
    (targetABC : realCData.Index (a + b) c)
    (sourceAB : realCData.Index a b)
    (sourceABC : realCData.Index (a + b) c)
    (q : ℝ) (x : Coeff a) (y : Coeff b) (z : Coeff c) :
    leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
        x (Coeff.smul b q y) z =
      Coeff.smul (a + b + c) q
        (leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
          x y z) := by
  simp_rw [leftRouteCoeff_eq_fusionCoefficient]
  rw [FusionTableLaws.fusionCoefficient_smul_right,
    FusionTableLaws.fusionCoefficient_smul_left]

private theorem leftRouteCoeff_smul_third (a b c : ZMod 8)
    (targetAB : realCData.Index a b)
    (targetABC : realCData.Index (a + b) c)
    (sourceAB : realCData.Index a b)
    (sourceABC : realCData.Index (a + b) c)
    (q : ℝ) (x : Coeff a) (y : Coeff b) (z : Coeff c) :
    leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
        x y (Coeff.smul c q z) =
      Coeff.smul (a + b + c) q
        (leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
          x y z) := by
  simp_rw [leftRouteCoeff_eq_fusionCoefficient]
  rw [realRouteRowTwist_smul,
    FusionTableLaws.fusionCoefficient_smul_right]

private theorem leftRouteCoeff_one (a b c : ZMod 8)
    (targetAB : realCData.Index a b)
    (targetABC : realCData.Index (a + b) c)
    (sourceAB : realCData.Index a b)
    (sourceABC : realCData.Index (a + b) c) :
    leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
        (Coeff.one a) (Coeff.one b) (Coeff.one c) =
      if targetAB = sourceAB then
        if targetABC = sourceABC then Coeff.one (a + b + c)
        else Coeff.zero (a + b + c)
      else Coeff.zero (a + b + c) := by
  change FusionTable.Index a b at targetAB sourceAB
  change FusionTable.Index (a + b) c at targetABC sourceABC
  rw [leftRouteCoeff_eq_fusionCoefficient]
  rw [realRouteRowTwist_one,
    FusionTableLaws.fusionCoefficient_one]
  change fusionCoefficient (a + b) c targetABC sourceABC
      (if targetAB = sourceAB then Coeff.one (a + b)
        else Coeff.zero (a + b)) (Coeff.one c) =
    (if targetAB = sourceAB then
      if targetABC = sourceABC then Coeff.one (a + b + c)
      else Coeff.zero (a + b + c)
    else Coeff.zero (a + b + c) : Coeff (a + b + c))
  by_cases hAB : targetAB = sourceAB
  · rw [if_pos hAB, if_pos hAB]
    exact FusionTableLaws.fusionCoefficient_one
      (a + b) c targetABC sourceABC
  · rw [if_neg hAB, if_neg hAB,
      FusionTableLaws.fusionCoefficient_zero_left]

private theorem leftRouteCoeff_memGrade (a b c : ZMod 8)
    (i j k : ZMod 2)
    (targetAB : realCData.Index a b)
    (targetABC : realCData.Index (a + b) c)
    (sourceAB : realCData.Index a b)
    (sourceABC : realCData.Index (a + b) c)
    {x : Coeff a} {y : Coeff b} {z : Coeff c}
    (hx : Coeff.MemGrade a i x) (hy : Coeff.MemGrade b j y)
    (hz : Coeff.MemGrade c k z) :
    Coeff.MemGrade (a + b + c)
      (i + j + k + indexParity a b targetAB +
        indexParity (a + b) c targetABC + indexParity a b sourceAB +
        indexParity (a + b) c sourceABC)
      (leftRouteCoeff realCData a b c targetAB targetABC
        sourceAB sourceABC x y z) := by
  have hinner := FusionTableLaws.fusionCoefficient_memGrade a b i j
    targetAB sourceAB hx hy
  have htwist : Coeff.MemGrade c k
      (routeRowTwist realDData c (indexParity a b sourceAB) z) := by
    rw [realRouteRowTwist_of_memGrade c (indexParity a b sourceAB) k z hz]
    exact Coeff.memGrade_smul c k _ hz
  rw [leftRouteCoeff_eq_fusionCoefficient]
  have houter := FusionTableLaws.fusionCoefficient_memGrade
    (a + b) c
    (i + j + indexParity a b targetAB + indexParity a b sourceAB) k
    targetABC sourceABC hinner htwist
  simpa [add_assoc, add_comm, add_left_comm] using houter

/- Composing two left-route coefficient matrices first contracts the outer
`((a+b),c)` rows.  The outer Koszul sign depends on the middle `(a,b)` row;
the row twist contributes the same row term, so characteristic two cancels
it.  The remaining contraction is exactly the binary `(a,b)` law. -/
private theorem leftRouteCoeff_mul (a b c : ZMod 8)
    (i' j k j' : ZMod 2)
    (targetAB : realCData.Index a b)
    (targetABC : realCData.Index (a + b) c)
    (sourceAB : realCData.Index a b)
    (sourceABC : realCData.Index (a + b) c)
    (x x' : Coeff a) (y y' : Coeff b) (z z' : Coeff c)
    (hy : Coeff.MemGrade b j y) (hz : Coeff.MemGrade c k z)
    (hx' : Coeff.MemGrade a i' x') (hy' : Coeff.MemGrade b j' y') :
    (∑ middleAB : realCData.Index a b,
      ∑ middleABC : realCData.Index (a + b) c,
        Coeff.mul (a + b + c)
          (leftRouteCoeff realCData a b c targetAB targetABC
            middleAB middleABC x y z)
          (leftRouteCoeff realCData a b c middleAB middleABC
            sourceAB sourceABC x' y' z')) =
      Coeff.smul (a + b + c)
        (paritySign (j * i' + k * (i' + j')))
        (leftRouteCoeff realCData a b c targetAB targetABC
          sourceAB sourceABC (Coeff.mul a x x') (Coeff.mul b y y')
          (Coeff.mul c z z')) := by
  change FusionTable.Index a b at targetAB sourceAB
  change FusionTable.Index (a + b) c at targetABC sourceABC
  simp_rw [leftRouteCoeff_eq_fusionCoefficient]
  have htwist (middleAB : FusionTable.Index a b) :
      Coeff.MemGrade c k
        (routeRowTwist realDData c (indexParity a b middleAB) z) := by
    rw [realRouteRowTwist_of_memGrade c (indexParity a b middleAB) k z hz]
    exact Coeff.memGrade_smul c k _ hz
  have hinner' (middleAB : FusionTable.Index a b) :
      Coeff.MemGrade (a + b)
        (i' + j' + indexParity a b middleAB + indexParity a b sourceAB)
        (fusionCoefficient a b middleAB sourceAB x' y') :=
    FusionTableLaws.fusionCoefficient_memGrade a b i' j'
      middleAB sourceAB hx' hy'
  calc
    (∑ middleAB, ∑ middleABC,
        Coeff.mul (a + b + c)
          (fusionCoefficient (a + b) c targetABC middleABC
            (fusionCoefficient a b targetAB middleAB x y)
            (routeRowTwist realDData c (indexParity a b middleAB) z))
          (fusionCoefficient (a + b) c middleABC sourceABC
            (fusionCoefficient a b middleAB sourceAB x' y')
            (routeRowTwist realDData c (indexParity a b sourceAB) z'))) =
      ∑ middleAB,
        Coeff.smul (a + b + c)
          (paritySign
            (k * (i' + j' + indexParity a b middleAB +
              indexParity a b sourceAB)))
          (fusionCoefficient (a + b) c targetABC sourceABC
            (Coeff.mul (a + b)
              (fusionCoefficient a b targetAB middleAB x y)
              (fusionCoefficient a b middleAB sourceAB x' y'))
            (Coeff.mul c
              (routeRowTwist realDData c (indexParity a b middleAB) z)
              (routeRowTwist realDData c (indexParity a b sourceAB) z'))) := by
        apply Finset.sum_congr rfl
        intro middleAB _
        exact fusionCoefficient_mul_parity (a + b) c
          (i' + j' + indexParity a b middleAB + indexParity a b sourceAB) k
          targetABC sourceABC
          (fusionCoefficient a b targetAB middleAB x y)
          (fusionCoefficient a b middleAB sourceAB x' y')
          (routeRowTwist realDData c (indexParity a b middleAB) z)
          (routeRowTwist realDData c (indexParity a b sourceAB) z')
          (htwist middleAB) (hinner' middleAB)
    _ = ∑ middleAB,
        Coeff.smul (a + b + c) (paritySign (k * (i' + j')))
          (fusionCoefficient (a + b) c targetABC sourceABC
            (Coeff.mul (a + b)
              (fusionCoefficient a b targetAB middleAB x y)
              (fusionCoefficient a b middleAB sourceAB x' y'))
            (routeRowTwist realDData c (indexParity a b sourceAB)
              (Coeff.mul c z z'))) := by
        apply Finset.sum_congr rfl
        intro middleAB _
        rw [realRouteRowTwist_mul_left c
          (indexParity a b middleAB) (indexParity a b sourceAB) k z z' hz,
          FusionTableLaws.fusionCoefficient_smul_right,
          ← Coeff.mul_smul]
        rw [realTParitySign_route_left k (i' + j')
          (indexParity a b middleAB) (indexParity a b sourceAB)]
    _ = Coeff.smul (a + b + c) (paritySign (k * (i' + j')))
        (∑ middleAB,
          fusionCoefficient (a + b) c targetABC sourceABC
            (Coeff.mul (a + b)
              (fusionCoefficient a b targetAB middleAB x y)
              (fusionCoefficient a b middleAB sourceAB x' y'))
            (routeRowTwist realDData c (indexParity a b sourceAB)
              (Coeff.mul c z z'))) :=
      (realTCoeff_smul_sum (a + b + c) (paritySign (k * (i' + j'))) _).symm
    _ = Coeff.smul (a + b + c) (paritySign (k * (i' + j')))
        (fusionCoefficient (a + b) c targetABC sourceABC
          (∑ middleAB,
            Coeff.mul (a + b)
              (fusionCoefficient a b targetAB middleAB x y)
              (fusionCoefficient a b middleAB sourceAB x' y'))
          (routeRowTwist realDData c (indexParity a b sourceAB)
            (Coeff.mul c z z'))) := by
      congr 1
      exact (fusionCoefficient_sum_left (a + b) c targetABC sourceABC _ _).symm
    _ = Coeff.smul (a + b + c) (paritySign (k * (i' + j')))
        (fusionCoefficient (a + b) c targetABC sourceABC
          (Coeff.smul (a + b) (paritySign (j * i'))
            (fusionCoefficient a b targetAB sourceAB
              (Coeff.mul a x x') (Coeff.mul b y y')))
          (routeRowTwist realDData c (indexParity a b sourceAB)
            (Coeff.mul c z z'))) := by
      rw [fusionCoefficient_mul_parity a b i' j targetAB sourceAB
        x x' y y' hy hx']
    _ = Coeff.smul (a + b + c) (paritySign (k * (i' + j')))
        (Coeff.smul (a + b + c) (paritySign (j * i'))
          (fusionCoefficient (a + b) c targetABC sourceABC
            (fusionCoefficient a b targetAB sourceAB
              (Coeff.mul a x x') (Coeff.mul b y y'))
            (routeRowTwist realDData c (indexParity a b sourceAB)
              (Coeff.mul c z z')))) := by
      rw [FusionTableLaws.fusionCoefficient_smul_left]
    _ = Coeff.smul (a + b + c)
        (paritySign (j * i' + k * (i' + j')))
        (fusionCoefficient (a + b) c targetABC sourceABC
          (fusionCoefficient a b targetAB sourceAB
            (Coeff.mul a x x') (Coeff.mul b y y'))
          (routeRowTwist realDData c (indexParity a b sourceAB)
            (Coeff.mul c z z'))) := by
      rw [← Coeff.mul_smul, realTParitySign_left_total]

/-! ### Finite two-row matrix actions -/

/- The remaining route-module arguments are independent of the fusion table.
They are collected for an arbitrary two-row coefficient matrix and then
instantiated with the left and right route coefficients. -/
private def realTMatrixAction {e : ZMod 8} {n m : ℕ}
    (K : Fin n → Fin m → Fin n → Fin m → Coeff e)
    (x : Fin n → Fin m → Coeff e) : Fin n → Fin m → Coeff e :=
  fun target₁ target₂ =>
    CData.rawFinSum (realDData.algebra e) fun source₁ =>
      CData.rawFinSum (realDData.algebra e) fun source₂ =>
        Coeff.mul e (K target₁ target₂ source₁ source₂)
          (x source₁ source₂)

private theorem realTMatrixAction_eq_pair_sum {e : ZMod 8} {n m : ℕ}
    (K : Fin n → Fin m → Fin n → Fin m → Coeff e)
    (x : Fin n → Fin m → Coeff e) (target₁ : Fin n) (target₂ : Fin m) :
    realTMatrixAction K x target₁ target₂ =
      ∑ source : Fin n × Fin m,
        Coeff.mul e (K target₁ target₂ source.1 source.2)
          (x source.1 source.2) := by
  unfold realTMatrixAction
  simp_rw [realTRawFinSum_eq_sum]
  exact (Fintype.sum_prod_type' fun source₁ source₂ =>
    Coeff.mul e (K target₁ target₂ source₁ source₂)
      (x source₁ source₂)).symm

private theorem realTMatrixAction_kernel_zero {e : ZMod 8} {n m : ℕ}
    (K : Fin n → Fin m → Fin n → Fin m → Coeff e)
    (x : Fin n → Fin m → Coeff e)
    (hK : ∀ target₁ target₂ source₁ source₂,
      K target₁ target₂ source₁ source₂ = Coeff.zero e) :
    realTMatrixAction K x = fun _ _ => Coeff.zero e := by
  funext target₁ target₂
  rw [realTMatrixAction_eq_pair_sum]
  simp_rw [hK, Coeff.zero_mul]
  exact realTCoeff_sum_zero e

private theorem realTMatrixAction_kernel_add {e : ZMod 8} {n m : ℕ}
    (K L M : Fin n → Fin m → Fin n → Fin m → Coeff e)
    (x : Fin n → Fin m → Coeff e)
    (hK : ∀ target₁ target₂ source₁ source₂,
      K target₁ target₂ source₁ source₂ =
        Coeff.add e (L target₁ target₂ source₁ source₂)
          (M target₁ target₂ source₁ source₂)) :
    realTMatrixAction K x = fun target₁ target₂ =>
      Coeff.add e (realTMatrixAction L x target₁ target₂)
        (realTMatrixAction M x target₁ target₂) := by
  funext target₁ target₂
  simp_rw [realTMatrixAction_eq_pair_sum, hK, Coeff.add_mul]
  exact Finset.sum_add_distrib

private theorem realTMatrixAction_kernel_smul {e : ZMod 8} {n m : ℕ}
    (q : ℝ)
    (K L : Fin n → Fin m → Fin n → Fin m → Coeff e)
    (x : Fin n → Fin m → Coeff e)
    (hK : ∀ target₁ target₂ source₁ source₂,
      K target₁ target₂ source₁ source₂ =
        Coeff.smul e q (L target₁ target₂ source₁ source₂)) :
    realTMatrixAction K x = fun target₁ target₂ =>
      Coeff.smul e q (realTMatrixAction L x target₁ target₂) := by
  funext target₁ target₂
  simp_rw [realTMatrixAction_eq_pair_sum, hK, Coeff.smul_mul]
  exact (realTCoeff_smul_sum e q _).symm

private theorem realTMatrixAction_zero_module {e : ZMod 8} {n m : ℕ}
    (K : Fin n → Fin m → Fin n → Fin m → Coeff e) :
    realTMatrixAction K (fun _ _ => Coeff.zero e) =
      fun _ _ => Coeff.zero e := by
  funext target₁ target₂
  rw [realTMatrixAction_eq_pair_sum]
  simp_rw [Coeff.mul_zero]
  exact realTCoeff_sum_zero e

private theorem realTMatrixAction_add_module {e : ZMod 8} {n m : ℕ}
    (K : Fin n → Fin m → Fin n → Fin m → Coeff e)
    (x y : Fin n → Fin m → Coeff e) :
    realTMatrixAction K (fun source₁ source₂ =>
        Coeff.add e (x source₁ source₂) (y source₁ source₂)) =
      fun target₁ target₂ =>
        Coeff.add e (realTMatrixAction K x target₁ target₂)
          (realTMatrixAction K y target₁ target₂) := by
  funext target₁ target₂
  simp_rw [realTMatrixAction_eq_pair_sum, Coeff.mul_add]
  exact Finset.sum_add_distrib

private theorem realTMatrixAction_smul_module {e : ZMod 8} {n m : ℕ}
    (q : ℝ) (K : Fin n → Fin m → Fin n → Fin m → Coeff e)
    (x : Fin n → Fin m → Coeff e) :
    realTMatrixAction K (fun source₁ source₂ =>
        Coeff.smul e q (x source₁ source₂)) =
      fun target₁ target₂ =>
        Coeff.smul e q (realTMatrixAction K x target₁ target₂) := by
  funext target₁ target₂
  simp_rw [realTMatrixAction_eq_pair_sum, Coeff.mul_smul_right]
  exact (realTCoeff_smul_sum e q _).symm

private theorem realTCoeff_mul_neg (e : ZMod 8) (x y : Coeff e) :
    Coeff.mul e x (Coeff.neg e y) = Coeff.neg e (Coeff.mul e x y) := by
  apply (Coeff.semantic e).injective
  simp [Coeff.semantic_mul]

private theorem realTCoeff_neg_sum {I : Type*} [Fintype I]
    (e : ZMod 8) (f : I → Coeff e) :
    Coeff.neg e (∑ r, f r) = ∑ r, Coeff.neg e (f r) := by
  ext g
  simp only [Coeff.neg, Finset.sum_apply]
  symm
  apply Finset.sum_neg_distrib

private theorem realTMatrixAction_neg_module {e : ZMod 8} {n m : ℕ}
    (K : Fin n → Fin m → Fin n → Fin m → Coeff e)
    (x : Fin n → Fin m → Coeff e) :
    realTMatrixAction K
        (fun source₁ source₂ => Coeff.neg e (x source₁ source₂)) =
      fun target₁ target₂ =>
        Coeff.neg e (realTMatrixAction K x target₁ target₂) := by
  funext target₁ target₂
  simp_rw [realTMatrixAction_eq_pair_sum, realTCoeff_mul_neg]
  exact (realTCoeff_neg_sum e _).symm

private theorem realTMatrixAction_one {e : ZMod 8} {n m : ℕ}
    (K : Fin n → Fin m → Fin n → Fin m → Coeff e)
    (x : Fin n → Fin m → Coeff e)
    (hK : ∀ target₁ target₂ source₁ source₂,
      K target₁ target₂ source₁ source₂ =
        if target₁ = source₁ then
          if target₂ = source₂ then Coeff.one e else Coeff.zero e
        else Coeff.zero e) :
    realTMatrixAction K x = x := by
  funext target₁ target₂
  rw [realTMatrixAction_eq_pair_sum]
  classical
  rw [Fintype.sum_eq_single (target₁, target₂)]
  · rw [hK, if_pos rfl, if_pos rfl, Coeff.one_mul]
  · intro source hsource
    rw [hK]
    by_cases h₁ : target₁ = source.1
    · have h₂ : target₂ ≠ source.2 := by
        intro h₂
        apply hsource
        apply Prod.ext
        · exact h₁.symm
        · exact h₂.symm
      rw [if_pos h₁, if_neg h₂, Coeff.zero_mul]
      rfl
    · rw [if_neg h₁, Coeff.zero_mul]
      rfl

private theorem realTMatrixAction_comp {e : ZMod 8} {n m : ℕ}
    (q : ℝ)
    (K L M : Fin n → Fin m → Fin n → Fin m → Coeff e)
    (x : Fin n → Fin m → Coeff e)
    (hcomp : ∀ target₁ target₂ source₁ source₂,
      (∑ middle : Fin n × Fin m,
        Coeff.mul e
          (K target₁ target₂ middle.1 middle.2)
          (L middle.1 middle.2 source₁ source₂)) =
        Coeff.smul e q (M target₁ target₂ source₁ source₂)) :
    realTMatrixAction K (realTMatrixAction L x) =
      fun target₁ target₂ =>
        Coeff.smul e q (realTMatrixAction M x target₁ target₂) := by
  funext target₁ target₂
  simp_rw [realTMatrixAction_eq_pair_sum]
  calc
    (∑ middle : Fin n × Fin m,
        Coeff.mul e (K target₁ target₂ middle.1 middle.2)
          (∑ source : Fin n × Fin m,
            Coeff.mul e (L middle.1 middle.2 source.1 source.2)
              (x source.1 source.2))) =
      ∑ middle : Fin n × Fin m, ∑ source : Fin n × Fin m,
        Coeff.mul e (K target₁ target₂ middle.1 middle.2)
          (Coeff.mul e (L middle.1 middle.2 source.1 source.2)
            (x source.1 source.2)) := by
        apply Finset.sum_congr rfl
        intro middle _
        exact realTCoeff_mul_sum e _ _
    _ = ∑ source : Fin n × Fin m, ∑ middle : Fin n × Fin m,
        Coeff.mul e
          (Coeff.mul e (K target₁ target₂ middle.1 middle.2)
            (L middle.1 middle.2 source.1 source.2))
          (x source.1 source.2) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro source _
        apply Finset.sum_congr rfl
        intro middle _
        exact (Coeff.mul_assoc e _ _ _).symm
    _ = ∑ source : Fin n × Fin m,
        Coeff.mul e
          (∑ middle : Fin n × Fin m,
            Coeff.mul e (K target₁ target₂ middle.1 middle.2)
              (L middle.1 middle.2 source.1 source.2))
          (x source.1 source.2) := by
        apply Finset.sum_congr rfl
        intro source _
        exact (realTCoeff_sum_mul e _ _).symm
    _ = ∑ source : Fin n × Fin m,
        Coeff.smul e q
          (Coeff.mul e (M target₁ target₂ source.1 source.2)
            (x source.1 source.2)) := by
        apply Finset.sum_congr rfl
        intro source _
        rw [hcomp, Coeff.smul_mul]
    _ = Coeff.smul e q
        (∑ source : Fin n × Fin m,
          Coeff.mul e (M target₁ target₂ source.1 source.2)
            (x source.1 source.2)) :=
      (realTCoeff_smul_sum e q _).symm

private theorem realTMatrixAction_memGrade {e : ZMod 8} {n m : ℕ}
    (row₁ : Fin n → ZMod 2) (row₂ : Fin m → ZMod 2)
    (d l : ZMod 2)
    (K : Fin n → Fin m → Fin n → Fin m → Coeff e)
    (x : Fin n → Fin m → Coeff e)
    (hK : ∀ target₁ target₂ source₁ source₂,
      Coeff.MemGrade e
        (d + row₁ target₁ + row₂ target₂ +
          row₁ source₁ + row₂ source₂)
        (K target₁ target₂ source₁ source₂))
    (hx : ∀ source₁ source₂,
      Coeff.MemGrade e (l + row₁ source₁ + row₂ source₂)
        (x source₁ source₂)) :
    ∀ target₁ target₂,
      Coeff.MemGrade e (d + l + row₁ target₁ + row₂ target₂)
        (realTMatrixAction K x target₁ target₂) := by
  intro target₁ target₂
  rw [realTMatrixAction_eq_pair_sum]
  apply realTCoeff_sum_memGrade
  intro source
  have hproduct := Coeff.memGrade_mul e
    (d + row₁ target₁ + row₂ target₂ +
      row₁ source.1 + row₂ source.2)
    (l + row₁ source.1 + row₂ source.2)
    (hK target₁ target₂ source.1 source.2) (hx source.1 source.2)
  have hdegree :
      (d + row₁ target₁ + row₂ target₂ +
          row₁ source.1 + row₂ source.2) +
          (l + row₁ source.1 + row₂ source.2) =
        d + l + row₁ target₁ + row₂ target₂ := by
    calc
      _ = d + l + row₁ target₁ + row₂ target₂ +
          ((row₁ source.1 + row₂ source.2) +
            (row₁ source.1 + row₂ source.2)) := by abel
      _ = d + l + row₁ target₁ + row₂ target₂ := by
        rw [Coeff.add_self_eq_zero, add_zero]
  exact hdegree ▸ hproduct

private theorem realTMatrixAction_right_comm {e : ZMod 8} {n m : ℕ}
    (K : Fin n → Fin m → Fin n → Fin m → Coeff e)
    (x : Fin n → Fin m → Coeff e) (q : Coeff e) :
    (fun target₁ target₂ =>
      Coeff.mul e (realTMatrixAction K x target₁ target₂) q) =
      realTMatrixAction K
        (fun source₁ source₂ => Coeff.mul e (x source₁ source₂) q) := by
  funext target₁ target₂
  simp_rw [realTMatrixAction_eq_pair_sum]
  rw [realTCoeff_sum_mul]
  apply Finset.sum_congr rfl
  intro source _
  exact Coeff.mul_assoc e _ _ _

/-! ### Laws of the left-associated concrete route -/

/-- The exact executable left-route record satisfies the additive, graded,
and bimodule laws required by `TripleRouteLaws`. -/
theorem realLeftRouteLaws :
    TripleRouteLaws realDData realDLaws realLeftRouteData where
  add_assoc := by
    intro a b c x y z
    funext r s
    exact Coeff.add_assoc (a + b + c) (x r s) (y r s) (z r s)
  add_comm := by
    intro a b c x y
    funext r s
    exact Coeff.add_comm (a + b + c) (x r s) (y r s)
  zero_add := by
    intro a b c x
    funext r s
    exact Coeff.zero_add (a + b + c) (x r s)
  add_zero := by
    intro a b c x
    funext r s
    exact Coeff.add_zero (a + b + c) (x r s)
  neg_add := by
    intro a b c x
    funext r s
    exact Coeff.neg_add (a + b + c) (x r s)
  add_neg := by
    intro a b c x
    funext r s
    exact Coeff.add_neg (a + b + c) (x r s)

  one_smul := by
    intro a b c x
    funext r s
    exact Coeff.one_smul (a + b + c) (x r s)
  smul_assoc := by
    intro a b c q q' x
    funext r s
    exact Coeff.mul_smul (a + b + c) q q' (x r s)
  add_smul := by
    intro a b c q q' x
    funext r s
    exact Coeff.add_smul (a + b + c) q q' (x r s)
  smul_add := by
    intro a b c q x y
    funext r s
    exact Coeff.smul_add (a + b + c) q (x r s) (y r s)
  zero_smul := by
    intro a b c x
    funext r s
    exact Coeff.zero_smul (a + b + c) (x r s)
  smul_zero := by
    intro a b c q
    funext r s
    exact Coeff.smul_zero (a + b + c) q

  component_zero := by
    intro a b c i
    funext r s
    exact Coeff.component_zero (a + b + c)
      (i + indexParity a b r + indexParity (a + b) c s)
  component_add := by
    intro a b c i x y
    funext r s
    exact Coeff.component_add (a + b + c)
      (i + indexParity a b r + indexParity (a + b) c s) (x r s) (y r s)
  component_neg := by
    intro a b c i x
    funext r s
    exact Coeff.component_neg (a + b + c)
      (i + indexParity a b r + indexParity (a + b) c s) (x r s)
  component_smul := by
    intro a b c i q x
    funext r s
    exact Coeff.component_smul (a + b + c)
      (i + indexParity a b r + indexParity (a + b) c s) q (x r s)
  component_idem := by
    intro a b c i x
    funext r s
    exact Coeff.component_idem (a + b + c)
      (i + indexParity a b r + indexParity (a + b) c s) (x r s)
  component_complement := by
    intro a b c i x
    funext r s
    change Coeff.add (a + b + c)
      (Coeff.component (a + b + c)
        (i + indexParity a b r + indexParity (a + b) c s) (x r s))
      (Coeff.component (a + b + c)
        (i + 1 + indexParity a b r + indexParity (a + b) c s) (x r s)) =
      x r s
    simpa [add_assoc, add_comm, add_left_comm] using
      (Coeff.component_complement (a + b + c)
        (i + indexParity a b r + indexParity (a + b) c s) (x r s))
  grade_disjoint := by
    intro a b c i x hx hx'
    funext r s
    apply Coeff.memGrade_disjoint (a + b + c)
      (i + indexParity a b r + indexParity (a + b) c s)
    · apply (Coeff.component_eq_self_iff (a + b + c)
        (i + indexParity a b r + indexParity (a + b) c s) (x r s)).1
      exact congrFun (congrFun hx r) s
    · apply (Coeff.component_eq_self_iff (a + b + c)
        (i + indexParity a b r + indexParity (a + b) c s + 1) (x r s)).1
      have h := congrFun (congrFun hx' r) s
      change Coeff.component (a + b + c)
        (i + 1 + indexParity a b r + indexParity (a + b) c s) (x r s) =
          x r s at h
      simpa [add_assoc, add_comm, add_left_comm] using h

  left_zero_first := by
    intro a b c y z m
    change realTMatrixAction
      (fun targetAB targetABC sourceAB sourceABC =>
        leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
          (Coeff.zero a) y z) m = fun _ _ => Coeff.zero (a + b + c)
    apply realTMatrixAction_kernel_zero
    intro targetAB targetABC sourceAB sourceABC
    exact leftRouteCoeff_zero_first a b c targetAB targetABC sourceAB sourceABC y z
  left_zero_second := by
    intro a b c x z m
    change realTMatrixAction
      (fun targetAB targetABC sourceAB sourceABC =>
        leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
          x (Coeff.zero b) z) m = fun _ _ => Coeff.zero (a + b + c)
    apply realTMatrixAction_kernel_zero
    intro targetAB targetABC sourceAB sourceABC
    exact leftRouteCoeff_zero_second a b c targetAB targetABC sourceAB sourceABC x z
  left_zero_third := by
    intro a b c x y m
    change realTMatrixAction
      (fun targetAB targetABC sourceAB sourceABC =>
        leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
          x y (Coeff.zero c)) m = fun _ _ => Coeff.zero (a + b + c)
    apply realTMatrixAction_kernel_zero
    intro targetAB targetABC sourceAB sourceABC
    exact leftRouteCoeff_zero_third a b c targetAB targetABC sourceAB sourceABC x y
  left_zero_module := by
    intro a b c x y z
    change realTMatrixAction
      (fun targetAB targetABC sourceAB sourceABC =>
        leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
          x y z) (fun _ _ => Coeff.zero (a + b + c)) =
      fun _ _ => Coeff.zero (a + b + c)
    exact realTMatrixAction_zero_module _
  left_add_first := by
    intro a b c x x' y z m
    change realTMatrixAction
      (fun targetAB targetABC sourceAB sourceABC =>
        leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
          (Coeff.add a x x') y z) m = fun targetAB targetABC =>
      Coeff.add (a + b + c)
        (realTMatrixAction
          (fun targetAB targetABC sourceAB sourceABC =>
            leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
              x y z) m targetAB targetABC)
        (realTMatrixAction
          (fun targetAB targetABC sourceAB sourceABC =>
            leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
              x' y z) m targetAB targetABC)
    apply realTMatrixAction_kernel_add
    intro targetAB targetABC sourceAB sourceABC
    exact leftRouteCoeff_add_first a b c targetAB targetABC sourceAB sourceABC
      x x' y z
  left_add_second := by
    intro a b c x y y' z m
    change realTMatrixAction
      (fun targetAB targetABC sourceAB sourceABC =>
        leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
          x (Coeff.add b y y') z) m = fun targetAB targetABC =>
      Coeff.add (a + b + c)
        (realTMatrixAction
          (fun targetAB targetABC sourceAB sourceABC =>
            leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
              x y z) m targetAB targetABC)
        (realTMatrixAction
          (fun targetAB targetABC sourceAB sourceABC =>
            leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
              x y' z) m targetAB targetABC)
    apply realTMatrixAction_kernel_add
    intro targetAB targetABC sourceAB sourceABC
    exact leftRouteCoeff_add_second a b c targetAB targetABC sourceAB sourceABC
      x y y' z
  left_add_third := by
    intro a b c x y z z' m
    change realTMatrixAction
      (fun targetAB targetABC sourceAB sourceABC =>
        leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
          x y (Coeff.add c z z')) m = fun targetAB targetABC =>
      Coeff.add (a + b + c)
        (realTMatrixAction
          (fun targetAB targetABC sourceAB sourceABC =>
            leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
              x y z) m targetAB targetABC)
        (realTMatrixAction
          (fun targetAB targetABC sourceAB sourceABC =>
            leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
              x y z') m targetAB targetABC)
    apply realTMatrixAction_kernel_add
    intro targetAB targetABC sourceAB sourceABC
    exact leftRouteCoeff_add_third a b c targetAB targetABC sourceAB sourceABC
      x y z z'
  left_add_module := by
    intro a b c x y z m n
    change realTMatrixAction
      (fun targetAB targetABC sourceAB sourceABC =>
        leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
          x y z)
      (fun sourceAB sourceABC => Coeff.add (a + b + c)
        (m sourceAB sourceABC) (n sourceAB sourceABC)) =
      fun targetAB targetABC => Coeff.add (a + b + c)
        (realTMatrixAction
          (fun targetAB targetABC sourceAB sourceABC =>
            leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
              x y z) m targetAB targetABC)
        (realTMatrixAction
          (fun targetAB targetABC sourceAB sourceABC =>
            leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
              x y z) n targetAB targetABC)
    exact realTMatrixAction_add_module _ m n
  left_smul_first := by
    intro a b c q x y z m
    change realTMatrixAction
      (fun targetAB targetABC sourceAB sourceABC =>
        leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
          (Coeff.smul a q x) y z) m = fun targetAB targetABC =>
      Coeff.smul (a + b + c) q
        (realTMatrixAction
          (fun targetAB targetABC sourceAB sourceABC =>
            leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
              x y z) m targetAB targetABC)
    apply realTMatrixAction_kernel_smul
    intro targetAB targetABC sourceAB sourceABC
    exact leftRouteCoeff_smul_first a b c targetAB targetABC sourceAB sourceABC
      q x y z
  left_smul_second := by
    intro a b c q x y z m
    change realTMatrixAction
      (fun targetAB targetABC sourceAB sourceABC =>
        leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
          x (Coeff.smul b q y) z) m = fun targetAB targetABC =>
      Coeff.smul (a + b + c) q
        (realTMatrixAction
          (fun targetAB targetABC sourceAB sourceABC =>
            leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
              x y z) m targetAB targetABC)
    apply realTMatrixAction_kernel_smul
    intro targetAB targetABC sourceAB sourceABC
    exact leftRouteCoeff_smul_second a b c targetAB targetABC sourceAB sourceABC
      q x y z
  left_smul_third := by
    intro a b c q x y z m
    change realTMatrixAction
      (fun targetAB targetABC sourceAB sourceABC =>
        leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
          x y (Coeff.smul c q z)) m = fun targetAB targetABC =>
      Coeff.smul (a + b + c) q
        (realTMatrixAction
          (fun targetAB targetABC sourceAB sourceABC =>
            leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
              x y z) m targetAB targetABC)
    apply realTMatrixAction_kernel_smul
    intro targetAB targetABC sourceAB sourceABC
    exact leftRouteCoeff_smul_third a b c targetAB targetABC sourceAB sourceABC
      q x y z
  left_smul_module := by
    intro a b c q x y z m
    change realTMatrixAction
      (fun targetAB targetABC sourceAB sourceABC =>
        leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
          x y z)
      (fun sourceAB sourceABC => Coeff.smul (a + b + c) q
        (m sourceAB sourceABC)) = fun targetAB targetABC =>
      Coeff.smul (a + b + c) q
        (realTMatrixAction
          (fun targetAB targetABC sourceAB sourceABC =>
            leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
              x y z) m targetAB targetABC)
    exact realTMatrixAction_smul_module q _ m
  left_one := by
    intro a b c m
    change realTMatrixAction
      (fun targetAB targetABC sourceAB sourceABC =>
        leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
          (Coeff.one a) (Coeff.one b) (Coeff.one c)) m = m
    apply realTMatrixAction_one
    intro targetAB targetABC sourceAB sourceABC
    exact leftRouteCoeff_one a b c targetAB targetABC sourceAB sourceABC
  left_mul := by
    intro a b c i' j k j' x x' y y' z z' m hy hz hx' hy'
    have hyc := (Coeff.component_eq_self_iff b j y).1 hy
    have hzc := (Coeff.component_eq_self_iff c k z).1 hz
    have hx'c := (Coeff.component_eq_self_iff a i' x').1 hx'
    have hy'c := (Coeff.component_eq_self_iff b j' y').1 hy'
    change realTMatrixAction
      (fun targetAB targetABC sourceAB sourceABC =>
        leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
          x y z)
      (realTMatrixAction
        (fun targetAB targetABC sourceAB sourceABC =>
          leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
            x' y' z') m) = fun targetAB targetABC =>
      Coeff.smul (a + b + c)
        (paritySign (j * i' + k * (i' + j')))
        (realTMatrixAction
          (fun targetAB targetABC sourceAB sourceABC =>
            leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
              (Coeff.mul a x x') (Coeff.mul b y y') (Coeff.mul c z z'))
          m targetAB targetABC)
    apply realTMatrixAction_comp
    intro targetAB targetABC sourceAB sourceABC
    calc
      (∑ middle : realCData.Index a b × realCData.Index (a + b) c,
          Coeff.mul (a + b + c)
            (leftRouteCoeff realCData a b c targetAB targetABC
              middle.1 middle.2 x y z)
            (leftRouteCoeff realCData a b c middle.1 middle.2
              sourceAB sourceABC x' y' z')) =
        ∑ middleAB : realCData.Index a b,
          ∑ middleABC : realCData.Index (a + b) c,
            Coeff.mul (a + b + c)
              (leftRouteCoeff realCData a b c targetAB targetABC
                middleAB middleABC x y z)
              (leftRouteCoeff realCData a b c middleAB middleABC
                sourceAB sourceABC x' y' z') :=
        Fintype.sum_prod_type' (fun middleAB middleABC =>
          Coeff.mul (a + b + c)
            (show Coeff (a + b + c) from
              leftRouteCoeff realCData a b c targetAB targetABC
                middleAB middleABC x y z)
            (show Coeff (a + b + c) from
              leftRouteCoeff realCData a b c middleAB middleABC
                sourceAB sourceABC x' y' z'))
      _ = Coeff.smul (a + b + c)
          (paritySign (j * i' + k * (i' + j')))
          (leftRouteCoeff realCData a b c targetAB targetABC
            sourceAB sourceABC (Coeff.mul a x x') (Coeff.mul b y y')
            (Coeff.mul c z z')) :=
        leftRouteCoeff_mul a b c i' j k j' targetAB targetABC
          sourceAB sourceABC x x' y y' z z' hyc hzc hx'c hy'c
  left_memGrade := by
    intro a b c i j k l x y z m hx hy hz hm
    have hxc := (Coeff.component_eq_self_iff a i x).1 hx
    have hyc := (Coeff.component_eq_self_iff b j y).1 hy
    have hzc := (Coeff.component_eq_self_iff c k z).1 hz
    apply funext
    intro targetAB
    apply funext
    intro targetABC
    apply (Coeff.component_eq_self_iff (a + b + c)
      (i + j + k + l + indexParity a b targetAB +
        indexParity (a + b) c targetABC) _).2
    apply realTMatrixAction_memGrade
      (fun r => indexParity a b r) (fun s => indexParity (a + b) c s)
      (i + j + k) l
    · intro targetAB targetABC sourceAB sourceABC
      simpa [add_assoc, add_comm, add_left_comm] using
        (leftRouteCoeff_memGrade a b c i j k targetAB targetABC
          sourceAB sourceABC hxc hyc hzc)
    · intro sourceAB sourceABC
      apply (Coeff.component_eq_self_iff (a + b + c)
        (l + indexParity a b sourceAB + indexParity (a + b) c sourceABC)
        (m sourceAB sourceABC)).1
      exact congrFun (congrFun hm sourceAB) sourceABC

  right_zero_module := by
    intro a b c q
    funext r s
    exact Coeff.zero_mul (a + b + c) q
  right_zero_algebra := by
    intro a b c m
    funext r s
    exact Coeff.mul_zero (a + b + c) (m r s)
  right_add_module := by
    intro a b c m n q
    funext r s
    exact Coeff.add_mul (a + b + c) (m r s) (n r s) q
  right_add_algebra := by
    intro a b c m q q'
    funext r s
    exact Coeff.mul_add (a + b + c) (m r s) q q'
  right_smul_module := by
    intro a b c q m x
    funext r s
    exact Coeff.smul_mul (a + b + c) q (m r s) x
  right_smul_algebra := by
    intro a b c q m x
    funext r s
    exact Coeff.mul_smul_right (a + b + c) q (m r s) x
  right_one := by
    intro a b c m
    funext r s
    exact Coeff.mul_one (a + b + c) (m r s)
  right_assoc := by
    intro a b c m q q'
    funext r s
    exact Coeff.mul_assoc (a + b + c) (m r s) q q'
  right_memGrade := by
    intro a b c i j m q hm hq
    funext r s
    change Coeff.component (a + b + c)
      (i + j + indexParity a b r + indexParity (a + b) c s)
      (Coeff.mul (a + b + c) (m r s) q) =
        Coeff.mul (a + b + c) (m r s) q
    apply (Coeff.component_eq_self_iff (a + b + c)
      (i + j + indexParity a b r + indexParity (a + b) c s) _).2
    have hmrs : Coeff.MemGrade (a + b + c)
        (i + indexParity a b r + indexParity (a + b) c s) (m r s) := by
      apply (Coeff.component_eq_self_iff (a + b + c)
        (i + indexParity a b r + indexParity (a + b) c s) _).1
      exact congrFun (congrFun hm r) s
    have hqc : Coeff.MemGrade (a + b + c) j q :=
      (Coeff.component_eq_self_iff (a + b + c) j q).1 hq
    simpa [add_assoc, add_comm, add_left_comm] using
      (Coeff.memGrade_mul (a + b + c)
        (i + indexParity a b r + indexParity (a + b) c s) j hmrs hqc)
  actions_comm := by
    intro a b c x y z m q
    change (fun targetAB targetABC =>
      Coeff.mul (a + b + c)
        (realTMatrixAction
          (fun targetAB targetABC sourceAB sourceABC =>
            leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
              x y z) m targetAB targetABC) q) =
      realTMatrixAction
        (fun targetAB targetABC sourceAB sourceABC =>
          leftRouteCoeff realCData a b c targetAB targetABC sourceAB sourceABC
            x y z)
        (fun sourceAB sourceABC => Coeff.mul (a + b + c)
          (m sourceAB sourceABC) q)
    exact realTMatrixAction_right_comm _ m q

/-! ### Coefficient laws of the right-associated route -/

/- Before the endpoint associativity cast, the right coefficient is an
ordinary nested pair of binary fusion coefficients at `a + (b + c)`. -/
private def realRightRouteCoeffRaw (a b c : ZMod 8)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c))
    (x : Coeff a) (y : Coeff b) (z : Coeff c) : Coeff (a + (b + c)) :=
  fusionCoefficient a (b + c) targetABC sourceABC
    (routeRowTwist realDData a (indexParity b c targetBC) x)
    (fusionCoefficient b c targetBC sourceBC y z)

private theorem rightRouteCoeff_eq_cast (a b c : ZMod 8)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c))
    (x : Coeff a) (y : Coeff b) (z : Coeff c) :
    rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC x y z =
      realCoeffCast (_root_.add_assoc a b c).symm
        (realRightRouteCoeffRaw a b c targetBC targetABC sourceBC sourceABC
          x y z) :=
  rfl

private theorem rightRouteCoeffRaw_zero_first (a b c : ZMod 8)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c))
    (y : Coeff b) (z : Coeff c) :
    realRightRouteCoeffRaw a b c targetBC targetABC sourceBC sourceABC
        (Coeff.zero a) y z = Coeff.zero (a + (b + c)) := by
  unfold realRightRouteCoeffRaw
  rw [realRouteRowTwist_zero,
    FusionTableLaws.fusionCoefficient_zero_left]

private theorem rightRouteCoeffRaw_zero_second (a b c : ZMod 8)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c))
    (x : Coeff a) (z : Coeff c) :
    realRightRouteCoeffRaw a b c targetBC targetABC sourceBC sourceABC
        x (Coeff.zero b) z = Coeff.zero (a + (b + c)) := by
  unfold realRightRouteCoeffRaw
  rw [FusionTableLaws.fusionCoefficient_zero_left,
    FusionTableLaws.fusionCoefficient_zero_right]

private theorem rightRouteCoeffRaw_zero_third (a b c : ZMod 8)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c))
    (x : Coeff a) (y : Coeff b) :
    realRightRouteCoeffRaw a b c targetBC targetABC sourceBC sourceABC
        x y (Coeff.zero c) = Coeff.zero (a + (b + c)) := by
  unfold realRightRouteCoeffRaw
  rw [FusionTableLaws.fusionCoefficient_zero_right,
    FusionTableLaws.fusionCoefficient_zero_right]

private theorem rightRouteCoeffRaw_add_first (a b c : ZMod 8)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c))
    (x x' : Coeff a) (y : Coeff b) (z : Coeff c) :
    realRightRouteCoeffRaw a b c targetBC targetABC sourceBC sourceABC
        (Coeff.add a x x') y z =
      Coeff.add (a + (b + c))
        (realRightRouteCoeffRaw a b c targetBC targetABC sourceBC sourceABC
          x y z)
        (realRightRouteCoeffRaw a b c targetBC targetABC sourceBC sourceABC
          x' y z) := by
  unfold realRightRouteCoeffRaw
  rw [realRouteRowTwist_add,
    FusionTableLaws.fusionCoefficient_add_left]

private theorem rightRouteCoeffRaw_add_second (a b c : ZMod 8)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c))
    (x : Coeff a) (y y' : Coeff b) (z : Coeff c) :
    realRightRouteCoeffRaw a b c targetBC targetABC sourceBC sourceABC
        x (Coeff.add b y y') z =
      Coeff.add (a + (b + c))
        (realRightRouteCoeffRaw a b c targetBC targetABC sourceBC sourceABC
          x y z)
        (realRightRouteCoeffRaw a b c targetBC targetABC sourceBC sourceABC
          x y' z) := by
  unfold realRightRouteCoeffRaw
  rw [FusionTableLaws.fusionCoefficient_add_left,
    FusionTableLaws.fusionCoefficient_add_right]

private theorem rightRouteCoeffRaw_add_third (a b c : ZMod 8)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c))
    (x : Coeff a) (y : Coeff b) (z z' : Coeff c) :
    realRightRouteCoeffRaw a b c targetBC targetABC sourceBC sourceABC
        x y (Coeff.add c z z') =
      Coeff.add (a + (b + c))
        (realRightRouteCoeffRaw a b c targetBC targetABC sourceBC sourceABC
          x y z)
        (realRightRouteCoeffRaw a b c targetBC targetABC sourceBC sourceABC
          x y z') := by
  unfold realRightRouteCoeffRaw
  rw [FusionTableLaws.fusionCoefficient_add_right,
    FusionTableLaws.fusionCoefficient_add_right]

private theorem rightRouteCoeffRaw_smul_first (a b c : ZMod 8)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c))
    (q : ℝ) (x : Coeff a) (y : Coeff b) (z : Coeff c) :
    realRightRouteCoeffRaw a b c targetBC targetABC sourceBC sourceABC
        (Coeff.smul a q x) y z =
      Coeff.smul (a + (b + c)) q
        (realRightRouteCoeffRaw a b c targetBC targetABC sourceBC sourceABC
          x y z) := by
  unfold realRightRouteCoeffRaw
  rw [realRouteRowTwist_smul,
    FusionTableLaws.fusionCoefficient_smul_left]

private theorem rightRouteCoeffRaw_smul_second (a b c : ZMod 8)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c))
    (q : ℝ) (x : Coeff a) (y : Coeff b) (z : Coeff c) :
    realRightRouteCoeffRaw a b c targetBC targetABC sourceBC sourceABC
        x (Coeff.smul b q y) z =
      Coeff.smul (a + (b + c)) q
        (realRightRouteCoeffRaw a b c targetBC targetABC sourceBC sourceABC
          x y z) := by
  unfold realRightRouteCoeffRaw
  rw [FusionTableLaws.fusionCoefficient_smul_left,
    FusionTableLaws.fusionCoefficient_smul_right]

private theorem rightRouteCoeffRaw_smul_third (a b c : ZMod 8)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c))
    (q : ℝ) (x : Coeff a) (y : Coeff b) (z : Coeff c) :
    realRightRouteCoeffRaw a b c targetBC targetABC sourceBC sourceABC
        x y (Coeff.smul c q z) =
      Coeff.smul (a + (b + c)) q
        (realRightRouteCoeffRaw a b c targetBC targetABC sourceBC sourceABC
          x y z) := by
  unfold realRightRouteCoeffRaw
  rw [FusionTableLaws.fusionCoefficient_smul_right,
    FusionTableLaws.fusionCoefficient_smul_right]

private theorem rightRouteCoeffRaw_one (a b c : ZMod 8)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c)) :
    realRightRouteCoeffRaw a b c targetBC targetABC sourceBC sourceABC
        (Coeff.one a) (Coeff.one b) (Coeff.one c) =
      if targetBC = sourceBC then
        if targetABC = sourceABC then Coeff.one (a + (b + c))
        else Coeff.zero (a + (b + c))
      else Coeff.zero (a + (b + c)) := by
  change FusionTable.Index b c at targetBC sourceBC
  change FusionTable.Index a (b + c) at targetABC sourceABC
  unfold realRightRouteCoeffRaw
  rw [realRouteRowTwist_one,
    FusionTableLaws.fusionCoefficient_one]
  change fusionCoefficient a (b + c) targetABC sourceABC (Coeff.one a)
      (if targetBC = sourceBC then Coeff.one (b + c) else Coeff.zero (b + c)) =
    (if targetBC = sourceBC then
      if targetABC = sourceABC then Coeff.one (a + (b + c))
      else Coeff.zero (a + (b + c))
    else Coeff.zero (a + (b + c)) : Coeff (a + (b + c)))
  by_cases hBC : targetBC = sourceBC
  · rw [if_pos hBC, if_pos hBC]
    exact FusionTableLaws.fusionCoefficient_one a (b + c) targetABC sourceABC
  · rw [if_neg hBC, if_neg hBC,
      FusionTableLaws.fusionCoefficient_zero_right]

private theorem rightRouteCoeffRaw_memGrade (a b c : ZMod 8)
    (i j k : ZMod 2)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c))
    {x : Coeff a} {y : Coeff b} {z : Coeff c}
    (hx : Coeff.MemGrade a i x) (hy : Coeff.MemGrade b j y)
    (hz : Coeff.MemGrade c k z) :
    Coeff.MemGrade (a + (b + c))
      (i + j + k + indexParity b c targetBC +
        indexParity a (b + c) targetABC + indexParity b c sourceBC +
        indexParity a (b + c) sourceABC)
      (realRightRouteCoeffRaw a b c targetBC targetABC sourceBC sourceABC
        x y z) := by
  have htwist : Coeff.MemGrade a i
      (routeRowTwist realDData a (indexParity b c targetBC) x) := by
    rw [realRouteRowTwist_of_memGrade a (indexParity b c targetBC) i x hx]
    exact Coeff.memGrade_smul a i _ hx
  have hinner := FusionTableLaws.fusionCoefficient_memGrade b c j k
    targetBC sourceBC hy hz
  unfold realRightRouteCoeffRaw
  have houter := FusionTableLaws.fusionCoefficient_memGrade a (b + c)
    i (j + k + indexParity b c targetBC + indexParity b c sourceBC)
    targetABC sourceABC htwist hinner
  simpa [add_assoc, add_comm, add_left_comm] using houter

/- For the right route the outer contraction is at `(a,b+c)`.  Its row
term is cancelled by the target-row twist on the `a` input; the remaining
middle contraction is the binary `(b,c)` multiplication law. -/
private theorem rightRouteCoeffRaw_mul (a b c : ZMod 8)
    (i' j k j' : ZMod 2)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c))
    (x x' : Coeff a) (y y' : Coeff b) (z z' : Coeff c)
    (hy : Coeff.MemGrade b j y) (hz : Coeff.MemGrade c k z)
    (hx' : Coeff.MemGrade a i' x') (hy' : Coeff.MemGrade b j' y') :
    (∑ middleBC : realCData.Index b c,
      ∑ middleABC : realCData.Index a (b + c),
        Coeff.mul (a + (b + c))
          (realRightRouteCoeffRaw a b c targetBC targetABC
            middleBC middleABC x y z)
          (realRightRouteCoeffRaw a b c middleBC middleABC
            sourceBC sourceABC x' y' z')) =
      Coeff.smul (a + (b + c))
        (paritySign (j * i' + k * (i' + j')))
        (realRightRouteCoeffRaw a b c targetBC targetABC
          sourceBC sourceABC (Coeff.mul a x x') (Coeff.mul b y y')
          (Coeff.mul c z z')) := by
  change FusionTable.Index b c at targetBC sourceBC
  change FusionTable.Index a (b + c) at targetABC sourceABC
  simp_rw [realRightRouteCoeffRaw]
  have hinner (middleBC : FusionTable.Index b c) :
      Coeff.MemGrade (b + c)
        (j + k + indexParity b c targetBC + indexParity b c middleBC)
        (fusionCoefficient b c targetBC middleBC y z) :=
    FusionTableLaws.fusionCoefficient_memGrade b c j k
      targetBC middleBC hy hz
  have htwist' (middleBC : FusionTable.Index b c) :
      Coeff.MemGrade a i'
        (routeRowTwist realDData a (indexParity b c middleBC) x') := by
    rw [realRouteRowTwist_of_memGrade a (indexParity b c middleBC) i' x' hx']
    exact Coeff.memGrade_smul a i' _ hx'
  calc
    (∑ middleBC, ∑ middleABC,
        Coeff.mul (a + (b + c))
          (fusionCoefficient a (b + c) targetABC middleABC
            (routeRowTwist realDData a (indexParity b c targetBC) x)
            (fusionCoefficient b c targetBC middleBC y z))
          (fusionCoefficient a (b + c) middleABC sourceABC
            (routeRowTwist realDData a (indexParity b c middleBC) x')
            (fusionCoefficient b c middleBC sourceBC y' z'))) =
      ∑ middleBC,
        Coeff.smul (a + (b + c))
          (paritySign
            ((j + k + indexParity b c targetBC +
              indexParity b c middleBC) * i'))
          (fusionCoefficient a (b + c) targetABC sourceABC
            (Coeff.mul a
              (routeRowTwist realDData a (indexParity b c targetBC) x)
              (routeRowTwist realDData a (indexParity b c middleBC) x'))
            (Coeff.mul (b + c)
              (fusionCoefficient b c targetBC middleBC y z)
              (fusionCoefficient b c middleBC sourceBC y' z'))) := by
        apply Finset.sum_congr rfl
        intro middleBC _
        exact fusionCoefficient_mul_parity a (b + c) i'
          (j + k + indexParity b c targetBC + indexParity b c middleBC)
          targetABC sourceABC
          (routeRowTwist realDData a (indexParity b c targetBC) x)
          (routeRowTwist realDData a (indexParity b c middleBC) x')
          (fusionCoefficient b c targetBC middleBC y z)
          (fusionCoefficient b c middleBC sourceBC y' z')
          (hinner middleBC) (htwist' middleBC)
    _ = ∑ middleBC,
        Coeff.smul (a + (b + c)) (paritySign ((j + k) * i'))
          (fusionCoefficient a (b + c) targetABC sourceABC
            (routeRowTwist realDData a (indexParity b c targetBC)
              (Coeff.mul a x x'))
            (Coeff.mul (b + c)
              (fusionCoefficient b c targetBC middleBC y z)
              (fusionCoefficient b c middleBC sourceBC y' z'))) := by
        apply Finset.sum_congr rfl
        intro middleBC _
        rw [realRouteRowTwist_mul_right a
          (indexParity b c targetBC) (indexParity b c middleBC) i' x x' hx',
          FusionTableLaws.fusionCoefficient_smul_left,
          ← Coeff.mul_smul]
        rw [realTParitySign_route_right (j + k) i'
          (indexParity b c targetBC) (indexParity b c middleBC)]
    _ = Coeff.smul (a + (b + c)) (paritySign ((j + k) * i'))
        (∑ middleBC,
          fusionCoefficient a (b + c) targetABC sourceABC
            (routeRowTwist realDData a (indexParity b c targetBC)
              (Coeff.mul a x x'))
            (Coeff.mul (b + c)
              (fusionCoefficient b c targetBC middleBC y z)
              (fusionCoefficient b c middleBC sourceBC y' z'))) :=
      (realTCoeff_smul_sum (a + (b + c)) (paritySign ((j + k) * i')) _).symm
    _ = Coeff.smul (a + (b + c)) (paritySign ((j + k) * i'))
        (fusionCoefficient a (b + c) targetABC sourceABC
          (routeRowTwist realDData a (indexParity b c targetBC)
            (Coeff.mul a x x'))
          (∑ middleBC,
            Coeff.mul (b + c)
              (fusionCoefficient b c targetBC middleBC y z)
              (fusionCoefficient b c middleBC sourceBC y' z'))) := by
      congr 1
      exact (fusionCoefficient_sum_right a (b + c) targetABC sourceABC _ _).symm
    _ = Coeff.smul (a + (b + c)) (paritySign ((j + k) * i'))
        (fusionCoefficient a (b + c) targetABC sourceABC
          (routeRowTwist realDData a (indexParity b c targetBC)
            (Coeff.mul a x x'))
          (Coeff.smul (b + c) (paritySign (k * j'))
            (fusionCoefficient b c targetBC sourceBC
              (Coeff.mul b y y') (Coeff.mul c z z')))) := by
      rw [fusionCoefficient_mul_parity b c j' k targetBC sourceBC
        y y' z z' hz hy']
    _ = Coeff.smul (a + (b + c)) (paritySign ((j + k) * i'))
        (Coeff.smul (a + (b + c)) (paritySign (k * j'))
          (fusionCoefficient a (b + c) targetABC sourceABC
            (routeRowTwist realDData a (indexParity b c targetBC)
              (Coeff.mul a x x'))
            (fusionCoefficient b c targetBC sourceBC
              (Coeff.mul b y y') (Coeff.mul c z z')))) := by
      rw [FusionTableLaws.fusionCoefficient_smul_right]
    _ = Coeff.smul (a + (b + c))
        (paritySign (j * i' + k * (i' + j')))
        (fusionCoefficient a (b + c) targetABC sourceABC
          (routeRowTwist realDData a (indexParity b c targetBC)
            (Coeff.mul a x x'))
          (fusionCoefficient b c targetBC sourceBC
            (Coeff.mul b y y') (Coeff.mul c z z'))) := by
      rw [← Coeff.mul_smul, realTParitySign_right_total]

/- The public right coefficient is the raw coefficient transported to the
left-associated endpoint label.  Equality induction supplies preservation
of zero, addition, scalar multiplication, multiplication, and grading. -/
private theorem rightRouteCoeff_zero_first (a b c : ZMod 8)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c))
    (y : Coeff b) (z : Coeff c) :
    rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
        (Coeff.zero a) y z = Coeff.zero (a + b + c) := by
  rw [rightRouteCoeff_eq_cast, rightRouteCoeffRaw_zero_first,
    realCoeffCast_zero]

private theorem rightRouteCoeff_zero_second (a b c : ZMod 8)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c))
    (x : Coeff a) (z : Coeff c) :
    rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
        x (Coeff.zero b) z = Coeff.zero (a + b + c) := by
  rw [rightRouteCoeff_eq_cast, rightRouteCoeffRaw_zero_second,
    realCoeffCast_zero]

private theorem rightRouteCoeff_zero_third (a b c : ZMod 8)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c))
    (x : Coeff a) (y : Coeff b) :
    rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
        x y (Coeff.zero c) = Coeff.zero (a + b + c) := by
  rw [rightRouteCoeff_eq_cast, rightRouteCoeffRaw_zero_third,
    realCoeffCast_zero]

private theorem rightRouteCoeff_add_first (a b c : ZMod 8)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c))
    (x x' : Coeff a) (y : Coeff b) (z : Coeff c) :
    rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
        (Coeff.add a x x') y z =
      Coeff.add (a + b + c)
        (rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
          x y z)
        (rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
          x' y z) := by
  simp_rw [rightRouteCoeff_eq_cast]
  rw [rightRouteCoeffRaw_add_first, realCoeffCast_add]

private theorem rightRouteCoeff_add_second (a b c : ZMod 8)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c))
    (x : Coeff a) (y y' : Coeff b) (z : Coeff c) :
    rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
        x (Coeff.add b y y') z =
      Coeff.add (a + b + c)
        (rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
          x y z)
        (rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
          x y' z) := by
  simp_rw [rightRouteCoeff_eq_cast]
  rw [rightRouteCoeffRaw_add_second, realCoeffCast_add]

private theorem rightRouteCoeff_add_third (a b c : ZMod 8)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c))
    (x : Coeff a) (y : Coeff b) (z z' : Coeff c) :
    rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
        x y (Coeff.add c z z') =
      Coeff.add (a + b + c)
        (rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
          x y z)
        (rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
          x y z') := by
  simp_rw [rightRouteCoeff_eq_cast]
  rw [rightRouteCoeffRaw_add_third, realCoeffCast_add]

private theorem rightRouteCoeff_smul_first (a b c : ZMod 8)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c))
    (q : ℝ) (x : Coeff a) (y : Coeff b) (z : Coeff c) :
    rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
        (Coeff.smul a q x) y z =
      Coeff.smul (a + b + c) q
        (rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
          x y z) := by
  simp_rw [rightRouteCoeff_eq_cast]
  rw [rightRouteCoeffRaw_smul_first, realCoeffCast_smul]

private theorem rightRouteCoeff_smul_second (a b c : ZMod 8)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c))
    (q : ℝ) (x : Coeff a) (y : Coeff b) (z : Coeff c) :
    rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
        x (Coeff.smul b q y) z =
      Coeff.smul (a + b + c) q
        (rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
          x y z) := by
  simp_rw [rightRouteCoeff_eq_cast]
  rw [rightRouteCoeffRaw_smul_second, realCoeffCast_smul]

private theorem rightRouteCoeff_smul_third (a b c : ZMod 8)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c))
    (q : ℝ) (x : Coeff a) (y : Coeff b) (z : Coeff c) :
    rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
        x y (Coeff.smul c q z) =
      Coeff.smul (a + b + c) q
        (rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
          x y z) := by
  simp_rw [rightRouteCoeff_eq_cast]
  rw [rightRouteCoeffRaw_smul_third, realCoeffCast_smul]

private theorem rightRouteCoeff_one (a b c : ZMod 8)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c)) :
    rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
        (Coeff.one a) (Coeff.one b) (Coeff.one c) =
      if targetBC = sourceBC then
        if targetABC = sourceABC then Coeff.one (a + b + c)
        else Coeff.zero (a + b + c)
      else Coeff.zero (a + b + c) := by
  rw [rightRouteCoeff_eq_cast, rightRouteCoeffRaw_one]
  by_cases hBC : targetBC = sourceBC
  · rw [if_pos hBC, if_pos hBC]
    by_cases hABC : targetABC = sourceABC
    · rw [if_pos hABC, if_pos hABC, realCoeffCast_one]
    · rw [if_neg hABC, if_neg hABC, realCoeffCast_zero]
  · rw [if_neg hBC, if_neg hBC, realCoeffCast_zero]

private theorem rightRouteCoeff_memGrade (a b c : ZMod 8)
    (i j k : ZMod 2)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c))
    {x : Coeff a} {y : Coeff b} {z : Coeff c}
    (hx : Coeff.MemGrade a i x) (hy : Coeff.MemGrade b j y)
    (hz : Coeff.MemGrade c k z) :
    Coeff.MemGrade (a + b + c)
      (i + j + k + indexParity b c targetBC +
        indexParity a (b + c) targetABC + indexParity b c sourceBC +
        indexParity a (b + c) sourceABC)
      (rightRouteCoeff realCData a b c targetBC targetABC
        sourceBC sourceABC x y z) := by
  rw [rightRouteCoeff_eq_cast]
  exact realCoeffCast_memGrade (_root_.add_assoc a b c).symm _
    (rightRouteCoeffRaw_memGrade a b c i j k targetBC targetABC
      sourceBC sourceABC hx hy hz)

private theorem rightRouteCoeff_mul (a b c : ZMod 8)
    (i' j k j' : ZMod 2)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c))
    (x x' : Coeff a) (y y' : Coeff b) (z z' : Coeff c)
    (hy : Coeff.MemGrade b j y) (hz : Coeff.MemGrade c k z)
    (hx' : Coeff.MemGrade a i' x') (hy' : Coeff.MemGrade b j' y') :
    (∑ middleBC : realCData.Index b c,
      ∑ middleABC : realCData.Index a (b + c),
        Coeff.mul (a + b + c)
          (rightRouteCoeff realCData a b c targetBC targetABC
            middleBC middleABC x y z)
          (rightRouteCoeff realCData a b c middleBC middleABC
            sourceBC sourceABC x' y' z')) =
      Coeff.smul (a + b + c)
        (paritySign (j * i' + k * (i' + j')))
        (rightRouteCoeff realCData a b c targetBC targetABC
          sourceBC sourceABC (Coeff.mul a x x') (Coeff.mul b y y')
          (Coeff.mul c z z')) := by
  simp_rw [rightRouteCoeff_eq_cast]
  calc
    (∑ middleBC, ∑ middleABC,
        Coeff.mul (a + b + c)
          (realCoeffCast (_root_.add_assoc a b c).symm
            (realRightRouteCoeffRaw a b c targetBC targetABC
              middleBC middleABC x y z))
          (realCoeffCast (_root_.add_assoc a b c).symm
            (realRightRouteCoeffRaw a b c middleBC middleABC
              sourceBC sourceABC x' y' z'))) =
      ∑ middleBC, ∑ middleABC,
        realCoeffCast (_root_.add_assoc a b c).symm
          (Coeff.mul (a + (b + c))
            (realRightRouteCoeffRaw a b c targetBC targetABC
              middleBC middleABC x y z)
            (realRightRouteCoeffRaw a b c middleBC middleABC
              sourceBC sourceABC x' y' z')) := by
        apply Finset.sum_congr rfl
        intro middleBC _
        apply Finset.sum_congr rfl
        intro middleABC _
        exact (realCoeffCast_mul (_root_.add_assoc a b c).symm _ _).symm
    _ = ∑ middleBC,
        realCoeffCast (_root_.add_assoc a b c).symm
          (∑ middleABC,
            Coeff.mul (a + (b + c))
              (realRightRouteCoeffRaw a b c targetBC targetABC
                middleBC middleABC x y z)
              (realRightRouteCoeffRaw a b c middleBC middleABC
                sourceBC sourceABC x' y' z')) := by
        apply Finset.sum_congr rfl
        intro middleBC _
        exact (realCoeffCast_sum (_root_.add_assoc a b c).symm _).symm
    _ = realCoeffCast (_root_.add_assoc a b c).symm
        (∑ middleBC, ∑ middleABC,
          Coeff.mul (a + (b + c))
            (realRightRouteCoeffRaw a b c targetBC targetABC
              middleBC middleABC x y z)
            (realRightRouteCoeffRaw a b c middleBC middleABC
              sourceBC sourceABC x' y' z')) :=
      (realCoeffCast_sum (_root_.add_assoc a b c).symm _).symm
    _ = realCoeffCast (_root_.add_assoc a b c).symm
        (Coeff.smul (a + (b + c))
          (paritySign (j * i' + k * (i' + j')))
          (realRightRouteCoeffRaw a b c targetBC targetABC
            sourceBC sourceABC (Coeff.mul a x x') (Coeff.mul b y y')
            (Coeff.mul c z z'))) := by
      rw [rightRouteCoeffRaw_mul a b c i' j k j' targetBC targetABC
        sourceBC sourceABC x x' y y' z z' hy hz hx' hy']
    _ = Coeff.smul (a + b + c)
        (paritySign (j * i' + k * (i' + j')))
        (realCoeffCast (_root_.add_assoc a b c).symm
          (realRightRouteCoeffRaw a b c targetBC targetABC
            sourceBC sourceABC (Coeff.mul a x x') (Coeff.mul b y y')
            (Coeff.mul c z z'))) :=
      realCoeffCast_smul (_root_.add_assoc a b c).symm _ _

/-! ### Laws of the right-associated concrete route -/

/-- The exact executable right-route record satisfies the additive, graded,
and bimodule laws required by `TripleRouteLaws`. -/
theorem realRightRouteLaws :
    TripleRouteLaws realDData realDLaws realRightRouteData where
  add_assoc := by
    intro a b c x y z
    funext r s
    exact Coeff.add_assoc (a + b + c) (x r s) (y r s) (z r s)
  add_comm := by
    intro a b c x y
    funext r s
    exact Coeff.add_comm (a + b + c) (x r s) (y r s)
  zero_add := by
    intro a b c x
    funext r s
    exact Coeff.zero_add (a + b + c) (x r s)
  add_zero := by
    intro a b c x
    funext r s
    exact Coeff.add_zero (a + b + c) (x r s)
  neg_add := by
    intro a b c x
    funext r s
    exact Coeff.neg_add (a + b + c) (x r s)
  add_neg := by
    intro a b c x
    funext r s
    exact Coeff.add_neg (a + b + c) (x r s)

  one_smul := by
    intro a b c x
    funext r s
    exact Coeff.one_smul (a + b + c) (x r s)
  smul_assoc := by
    intro a b c q q' x
    funext r s
    exact Coeff.mul_smul (a + b + c) q q' (x r s)
  add_smul := by
    intro a b c q q' x
    funext r s
    exact Coeff.add_smul (a + b + c) q q' (x r s)
  smul_add := by
    intro a b c q x y
    funext r s
    exact Coeff.smul_add (a + b + c) q (x r s) (y r s)
  zero_smul := by
    intro a b c x
    funext r s
    exact Coeff.zero_smul (a + b + c) (x r s)
  smul_zero := by
    intro a b c q
    funext r s
    exact Coeff.smul_zero (a + b + c) q

  component_zero := by
    intro a b c i
    funext r s
    exact Coeff.component_zero (a + b + c)
      (i + indexParity b c r + indexParity a (b + c) s)
  component_add := by
    intro a b c i x y
    funext r s
    exact Coeff.component_add (a + b + c)
      (i + indexParity b c r + indexParity a (b + c) s) (x r s) (y r s)
  component_neg := by
    intro a b c i x
    funext r s
    exact Coeff.component_neg (a + b + c)
      (i + indexParity b c r + indexParity a (b + c) s) (x r s)
  component_smul := by
    intro a b c i q x
    funext r s
    exact Coeff.component_smul (a + b + c)
      (i + indexParity b c r + indexParity a (b + c) s) q (x r s)
  component_idem := by
    intro a b c i x
    funext r s
    exact Coeff.component_idem (a + b + c)
      (i + indexParity b c r + indexParity a (b + c) s) (x r s)
  component_complement := by
    intro a b c i x
    funext r s
    change Coeff.add (a + b + c)
      (Coeff.component (a + b + c)
        (i + indexParity b c r + indexParity a (b + c) s) (x r s))
      (Coeff.component (a + b + c)
        (i + 1 + indexParity b c r + indexParity a (b + c) s) (x r s)) =
      x r s
    simpa [add_assoc, add_comm, add_left_comm] using
      (Coeff.component_complement (a + b + c)
        (i + indexParity b c r + indexParity a (b + c) s) (x r s))
  grade_disjoint := by
    intro a b c i x hx hx'
    funext r s
    apply Coeff.memGrade_disjoint (a + b + c)
      (i + indexParity b c r + indexParity a (b + c) s)
    · apply (Coeff.component_eq_self_iff (a + b + c)
        (i + indexParity b c r + indexParity a (b + c) s) (x r s)).1
      exact congrFun (congrFun hx r) s
    · apply (Coeff.component_eq_self_iff (a + b + c)
        (i + indexParity b c r + indexParity a (b + c) s + 1) (x r s)).1
      have h := congrFun (congrFun hx' r) s
      change Coeff.component (a + b + c)
        (i + 1 + indexParity b c r + indexParity a (b + c) s) (x r s) =
          x r s at h
      simpa [add_assoc, add_comm, add_left_comm] using h

  left_zero_first := by
    intro a b c y z m
    change realTMatrixAction
      (fun targetBC targetABC sourceBC sourceABC =>
        rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
          (Coeff.zero a) y z) m = fun _ _ => Coeff.zero (a + b + c)
    apply realTMatrixAction_kernel_zero
    intro targetBC targetABC sourceBC sourceABC
    exact rightRouteCoeff_zero_first a b c targetBC targetABC sourceBC sourceABC y z
  left_zero_second := by
    intro a b c x z m
    change realTMatrixAction
      (fun targetBC targetABC sourceBC sourceABC =>
        rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
          x (Coeff.zero b) z) m = fun _ _ => Coeff.zero (a + b + c)
    apply realTMatrixAction_kernel_zero
    intro targetBC targetABC sourceBC sourceABC
    exact rightRouteCoeff_zero_second a b c targetBC targetABC sourceBC sourceABC x z
  left_zero_third := by
    intro a b c x y m
    change realTMatrixAction
      (fun targetBC targetABC sourceBC sourceABC =>
        rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
          x y (Coeff.zero c)) m = fun _ _ => Coeff.zero (a + b + c)
    apply realTMatrixAction_kernel_zero
    intro targetBC targetABC sourceBC sourceABC
    exact rightRouteCoeff_zero_third a b c targetBC targetABC sourceBC sourceABC x y
  left_zero_module := by
    intro a b c x y z
    change realTMatrixAction
      (fun targetBC targetABC sourceBC sourceABC =>
        rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
          x y z) (fun _ _ => Coeff.zero (a + b + c)) =
      fun _ _ => Coeff.zero (a + b + c)
    exact realTMatrixAction_zero_module _
  left_add_first := by
    intro a b c x x' y z m
    change realTMatrixAction
      (fun targetBC targetABC sourceBC sourceABC =>
        rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
          (Coeff.add a x x') y z) m = fun targetBC targetABC =>
      Coeff.add (a + b + c)
        (realTMatrixAction
          (fun targetBC targetABC sourceBC sourceABC =>
            rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
              x y z) m targetBC targetABC)
        (realTMatrixAction
          (fun targetBC targetABC sourceBC sourceABC =>
            rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
              x' y z) m targetBC targetABC)
    apply realTMatrixAction_kernel_add
    intro targetBC targetABC sourceBC sourceABC
    exact rightRouteCoeff_add_first a b c targetBC targetABC sourceBC sourceABC
      x x' y z
  left_add_second := by
    intro a b c x y y' z m
    change realTMatrixAction
      (fun targetBC targetABC sourceBC sourceABC =>
        rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
          x (Coeff.add b y y') z) m = fun targetBC targetABC =>
      Coeff.add (a + b + c)
        (realTMatrixAction
          (fun targetBC targetABC sourceBC sourceABC =>
            rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
              x y z) m targetBC targetABC)
        (realTMatrixAction
          (fun targetBC targetABC sourceBC sourceABC =>
            rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
              x y' z) m targetBC targetABC)
    apply realTMatrixAction_kernel_add
    intro targetBC targetABC sourceBC sourceABC
    exact rightRouteCoeff_add_second a b c targetBC targetABC sourceBC sourceABC
      x y y' z
  left_add_third := by
    intro a b c x y z z' m
    change realTMatrixAction
      (fun targetBC targetABC sourceBC sourceABC =>
        rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
          x y (Coeff.add c z z')) m = fun targetBC targetABC =>
      Coeff.add (a + b + c)
        (realTMatrixAction
          (fun targetBC targetABC sourceBC sourceABC =>
            rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
              x y z) m targetBC targetABC)
        (realTMatrixAction
          (fun targetBC targetABC sourceBC sourceABC =>
            rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
              x y z') m targetBC targetABC)
    apply realTMatrixAction_kernel_add
    intro targetBC targetABC sourceBC sourceABC
    exact rightRouteCoeff_add_third a b c targetBC targetABC sourceBC sourceABC
      x y z z'
  left_add_module := by
    intro a b c x y z m n
    change realTMatrixAction
      (fun targetBC targetABC sourceBC sourceABC =>
        rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
          x y z)
      (fun sourceBC sourceABC => Coeff.add (a + b + c)
        (m sourceBC sourceABC) (n sourceBC sourceABC)) =
      fun targetBC targetABC => Coeff.add (a + b + c)
        (realTMatrixAction
          (fun targetBC targetABC sourceBC sourceABC =>
            rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
              x y z) m targetBC targetABC)
        (realTMatrixAction
          (fun targetBC targetABC sourceBC sourceABC =>
            rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
              x y z) n targetBC targetABC)
    exact realTMatrixAction_add_module _ m n
  left_smul_first := by
    intro a b c q x y z m
    change realTMatrixAction
      (fun targetBC targetABC sourceBC sourceABC =>
        rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
          (Coeff.smul a q x) y z) m = fun targetBC targetABC =>
      Coeff.smul (a + b + c) q
        (realTMatrixAction
          (fun targetBC targetABC sourceBC sourceABC =>
            rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
              x y z) m targetBC targetABC)
    apply realTMatrixAction_kernel_smul
    intro targetBC targetABC sourceBC sourceABC
    exact rightRouteCoeff_smul_first a b c targetBC targetABC sourceBC sourceABC
      q x y z
  left_smul_second := by
    intro a b c q x y z m
    change realTMatrixAction
      (fun targetBC targetABC sourceBC sourceABC =>
        rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
          x (Coeff.smul b q y) z) m = fun targetBC targetABC =>
      Coeff.smul (a + b + c) q
        (realTMatrixAction
          (fun targetBC targetABC sourceBC sourceABC =>
            rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
              x y z) m targetBC targetABC)
    apply realTMatrixAction_kernel_smul
    intro targetBC targetABC sourceBC sourceABC
    exact rightRouteCoeff_smul_second a b c targetBC targetABC sourceBC sourceABC
      q x y z
  left_smul_third := by
    intro a b c q x y z m
    change realTMatrixAction
      (fun targetBC targetABC sourceBC sourceABC =>
        rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
          x y (Coeff.smul c q z)) m = fun targetBC targetABC =>
      Coeff.smul (a + b + c) q
        (realTMatrixAction
          (fun targetBC targetABC sourceBC sourceABC =>
            rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
              x y z) m targetBC targetABC)
    apply realTMatrixAction_kernel_smul
    intro targetBC targetABC sourceBC sourceABC
    exact rightRouteCoeff_smul_third a b c targetBC targetABC sourceBC sourceABC
      q x y z
  left_smul_module := by
    intro a b c q x y z m
    change realTMatrixAction
      (fun targetBC targetABC sourceBC sourceABC =>
        rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
          x y z)
      (fun sourceBC sourceABC => Coeff.smul (a + b + c) q
        (m sourceBC sourceABC)) = fun targetBC targetABC =>
      Coeff.smul (a + b + c) q
        (realTMatrixAction
          (fun targetBC targetABC sourceBC sourceABC =>
            rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
              x y z) m targetBC targetABC)
    exact realTMatrixAction_smul_module q _ m
  left_one := by
    intro a b c m
    change realTMatrixAction
      (fun targetBC targetABC sourceBC sourceABC =>
        rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
          (Coeff.one a) (Coeff.one b) (Coeff.one c)) m = m
    apply realTMatrixAction_one
    intro targetBC targetABC sourceBC sourceABC
    exact rightRouteCoeff_one a b c targetBC targetABC sourceBC sourceABC
  left_mul := by
    intro a b c i' j k j' x x' y y' z z' m hy hz hx' hy'
    have hyc := (Coeff.component_eq_self_iff b j y).1 hy
    have hzc := (Coeff.component_eq_self_iff c k z).1 hz
    have hx'c := (Coeff.component_eq_self_iff a i' x').1 hx'
    have hy'c := (Coeff.component_eq_self_iff b j' y').1 hy'
    change realTMatrixAction
      (fun targetBC targetABC sourceBC sourceABC =>
        rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
          x y z)
      (realTMatrixAction
        (fun targetBC targetABC sourceBC sourceABC =>
          rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
            x' y' z') m) = fun targetBC targetABC =>
      Coeff.smul (a + b + c)
        (paritySign (j * i' + k * (i' + j')))
        (realTMatrixAction
          (fun targetBC targetABC sourceBC sourceABC =>
            rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
              (Coeff.mul a x x') (Coeff.mul b y y') (Coeff.mul c z z'))
          m targetBC targetABC)
    apply realTMatrixAction_comp
    intro targetBC targetABC sourceBC sourceABC
    calc
      (∑ middle : realCData.Index b c × realCData.Index a (b + c),
          Coeff.mul (a + b + c)
            (rightRouteCoeff realCData a b c targetBC targetABC
              middle.1 middle.2 x y z)
            (rightRouteCoeff realCData a b c middle.1 middle.2
              sourceBC sourceABC x' y' z')) =
        ∑ middleBC : realCData.Index b c,
          ∑ middleABC : realCData.Index a (b + c),
            Coeff.mul (a + b + c)
              (rightRouteCoeff realCData a b c targetBC targetABC
                middleBC middleABC x y z)
              (rightRouteCoeff realCData a b c middleBC middleABC
                sourceBC sourceABC x' y' z') :=
        Fintype.sum_prod_type' (fun middleBC middleABC =>
          Coeff.mul (a + b + c)
            (show Coeff (a + b + c) from
              rightRouteCoeff realCData a b c targetBC targetABC
                middleBC middleABC x y z)
            (show Coeff (a + b + c) from
              rightRouteCoeff realCData a b c middleBC middleABC
                sourceBC sourceABC x' y' z'))
      _ = Coeff.smul (a + b + c)
          (paritySign (j * i' + k * (i' + j')))
          (rightRouteCoeff realCData a b c targetBC targetABC
            sourceBC sourceABC (Coeff.mul a x x') (Coeff.mul b y y')
            (Coeff.mul c z z')) :=
        rightRouteCoeff_mul a b c i' j k j' targetBC targetABC
          sourceBC sourceABC x x' y y' z z' hyc hzc hx'c hy'c
  left_memGrade := by
    intro a b c i j k l x y z m hx hy hz hm
    have hxc := (Coeff.component_eq_self_iff a i x).1 hx
    have hyc := (Coeff.component_eq_self_iff b j y).1 hy
    have hzc := (Coeff.component_eq_self_iff c k z).1 hz
    apply funext
    intro targetBC
    apply funext
    intro targetABC
    apply (Coeff.component_eq_self_iff (a + b + c)
      (i + j + k + l + indexParity b c targetBC +
        indexParity a (b + c) targetABC) _).2
    apply realTMatrixAction_memGrade
      (fun r => indexParity b c r) (fun s => indexParity a (b + c) s)
      (i + j + k) l
    · intro targetBC targetABC sourceBC sourceABC
      simpa [add_assoc, add_comm, add_left_comm] using
        (rightRouteCoeff_memGrade a b c i j k targetBC targetABC
          sourceBC sourceABC hxc hyc hzc)
    · intro sourceBC sourceABC
      apply (Coeff.component_eq_self_iff (a + b + c)
        (l + indexParity b c sourceBC + indexParity a (b + c) sourceABC)
        (m sourceBC sourceABC)).1
      exact congrFun (congrFun hm sourceBC) sourceABC

  right_zero_module := by
    intro a b c q
    funext r s
    exact Coeff.zero_mul (a + b + c) q
  right_zero_algebra := by
    intro a b c m
    funext r s
    exact Coeff.mul_zero (a + b + c) (m r s)
  right_add_module := by
    intro a b c m n q
    funext r s
    exact Coeff.add_mul (a + b + c) (m r s) (n r s) q
  right_add_algebra := by
    intro a b c m q q'
    funext r s
    exact Coeff.mul_add (a + b + c) (m r s) q q'
  right_smul_module := by
    intro a b c q m x
    funext r s
    exact Coeff.smul_mul (a + b + c) q (m r s) x
  right_smul_algebra := by
    intro a b c q m x
    funext r s
    exact Coeff.mul_smul_right (a + b + c) q (m r s) x
  right_one := by
    intro a b c m
    funext r s
    exact Coeff.mul_one (a + b + c) (m r s)
  right_assoc := by
    intro a b c m q q'
    funext r s
    exact Coeff.mul_assoc (a + b + c) (m r s) q q'
  right_memGrade := by
    intro a b c i j m q hm hq
    funext r s
    change Coeff.component (a + b + c)
      (i + j + indexParity b c r + indexParity a (b + c) s)
      (Coeff.mul (a + b + c) (m r s) q) =
        Coeff.mul (a + b + c) (m r s) q
    apply (Coeff.component_eq_self_iff (a + b + c)
      (i + j + indexParity b c r + indexParity a (b + c) s) _).2
    have hmrs : Coeff.MemGrade (a + b + c)
        (i + indexParity b c r + indexParity a (b + c) s) (m r s) := by
      apply (Coeff.component_eq_self_iff (a + b + c)
        (i + indexParity b c r + indexParity a (b + c) s) _).1
      exact congrFun (congrFun hm r) s
    have hqc : Coeff.MemGrade (a + b + c) j q :=
      (Coeff.component_eq_self_iff (a + b + c) j q).1 hq
    simpa [add_assoc, add_comm, add_left_comm] using
      (Coeff.memGrade_mul (a + b + c)
        (i + indexParity b c r + indexParity a (b + c) s) j hmrs hqc)
  actions_comm := by
    intro a b c x y z m q
    change (fun targetBC targetABC =>
      Coeff.mul (a + b + c)
        (realTMatrixAction
          (fun targetBC targetABC sourceBC sourceABC =>
            rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
              x y z) m targetBC targetABC) q) =
      realTMatrixAction
        (fun targetBC targetABC sourceBC sourceABC =>
          rightRouteCoeff realCData a b c targetBC targetABC sourceBC sourceABC
            x y z)
        (fun sourceBC sourceABC => Coeff.mul (a + b + c)
          (m sourceBC sourceABC) q)
    exact realTMatrixAction_right_comm _ m q

/-! ## Table-independent connector laws -/

/-! ### Coordinate presentations

Both concrete route carriers already are their advertised coordinate types,
and all four presentation maps stored in `realTData` are identities.  The
operation formulas below are therefore definitional equalities, not table
certificates. -/

theorem realT_left_ofCoord_toCoord (a b c : ZMod 8)
    (x : realTData.LeftCarrier a b c) :
    realTData.leftOfCoord a b c (realTData.leftToCoord a b c x) = x :=
  rfl

theorem realT_left_toCoord_ofCoord (a b c : ZMod 8)
    (x : LeftRouteCoordinates realCData a b c) :
    realTData.leftToCoord a b c (realTData.leftOfCoord a b c x) = x :=
  rfl

theorem realT_right_ofCoord_toCoord (a b c : ZMod 8)
    (x : realTData.RightCarrier a b c) :
    realTData.rightOfCoord a b c (realTData.rightToCoord a b c x) = x :=
  rfl

theorem realT_right_toCoord_ofCoord (a b c : ZMod 8)
    (x : RightRouteCoordinates realCData a b c) :
    realTData.rightToCoord a b c (realTData.rightOfCoord a b c x) = x :=
  rfl

theorem realT_left_toCoord_zero (a b c : ZMod 8) :
    realTData.leftToCoord a b c (realTData.leftRoute.zero a b c) =
      fun _ _ => (realDData.algebra (a + b + c)).zero :=
  rfl

theorem realT_left_toCoord_add (a b c : ZMod 8)
    (x y : realTData.LeftCarrier a b c) :
    realTData.leftToCoord a b c (realTData.leftRoute.add a b c x y) =
      fun r s => (realDData.algebra (a + b + c)).add
        (realTData.leftToCoord a b c x r s)
        (realTData.leftToCoord a b c y r s) :=
  rfl

theorem realT_left_toCoord_neg (a b c : ZMod 8)
    (x : realTData.LeftCarrier a b c) :
    realTData.leftToCoord a b c (realTData.leftRoute.neg a b c x) =
      fun r s => (realDData.algebra (a + b + c)).neg
        (realTData.leftToCoord a b c x r s) :=
  rfl

theorem realT_left_toCoord_smul (a b c : ZMod 8) (q : ℝ)
    (x : realTData.LeftCarrier a b c) :
    realTData.leftToCoord a b c (realTData.leftRoute.smul a b c q x) =
      fun r s => (realDData.algebra (a + b + c)).smul q
        (realTData.leftToCoord a b c x r s) :=
  rfl

theorem realT_left_toCoord_component (a b c : ZMod 8) (i : ZMod 2)
    (x : realTData.LeftCarrier a b c) :
    realTData.leftToCoord a b c (realTData.leftRoute.component a b c i x) =
      fun r s => (realDData.algebra (a + b + c)).component
        (i + realCData.rowParity a b r + realCData.rowParity (a + b) c s)
        (realTData.leftToCoord a b c x r s) :=
  rfl

theorem realT_left_toCoord_leftPure (a b c : ZMod 8)
    (x : (realDData.algebra a).carrier)
    (y : (realDData.algebra b).carrier)
    (z : (realDData.algebra c).carrier)
    (m : realTData.LeftCarrier a b c) :
    realTData.leftToCoord a b c
        (realTData.leftRoute.leftPure a b c x y z m) =
      fun targetAB targetABC =>
        CData.rawFinSum (realDData.algebra (a + b + c)) fun sourceAB =>
          CData.rawFinSum (realDData.algebra (a + b + c)) fun sourceABC =>
            (realDData.algebra (a + b + c)).mul
              (leftRouteCoeff realCData a b c targetAB targetABC
                sourceAB sourceABC x y z)
              (realTData.leftToCoord a b c m sourceAB sourceABC) :=
  rfl

theorem realT_left_toCoord_right (a b c : ZMod 8)
    (m : realTData.LeftCarrier a b c)
    (q : (realDData.algebra (a + b + c)).carrier) :
    realTData.leftToCoord a b c (realTData.leftRoute.right a b c m q) =
      fun r s => (realDData.algebra (a + b + c)).mul
        (realTData.leftToCoord a b c m r s) q :=
  rfl

theorem realT_right_toCoord_zero (a b c : ZMod 8) :
    realTData.rightToCoord a b c (realTData.rightRoute.zero a b c) =
      fun _ _ => (realDData.algebra (a + b + c)).zero :=
  rfl

theorem realT_right_toCoord_add (a b c : ZMod 8)
    (x y : realTData.RightCarrier a b c) :
    realTData.rightToCoord a b c (realTData.rightRoute.add a b c x y) =
      fun r s => (realDData.algebra (a + b + c)).add
        (realTData.rightToCoord a b c x r s)
        (realTData.rightToCoord a b c y r s) :=
  rfl

theorem realT_right_toCoord_neg (a b c : ZMod 8)
    (x : realTData.RightCarrier a b c) :
    realTData.rightToCoord a b c (realTData.rightRoute.neg a b c x) =
      fun r s => (realDData.algebra (a + b + c)).neg
        (realTData.rightToCoord a b c x r s) :=
  rfl

theorem realT_right_toCoord_smul (a b c : ZMod 8) (q : ℝ)
    (x : realTData.RightCarrier a b c) :
    realTData.rightToCoord a b c (realTData.rightRoute.smul a b c q x) =
      fun r s => (realDData.algebra (a + b + c)).smul q
        (realTData.rightToCoord a b c x r s) :=
  rfl

theorem realT_right_toCoord_component (a b c : ZMod 8) (i : ZMod 2)
    (x : realTData.RightCarrier a b c) :
    realTData.rightToCoord a b c (realTData.rightRoute.component a b c i x) =
      fun r s => (realDData.algebra (a + b + c)).component
        (i + realCData.rowParity b c r + realCData.rowParity a (b + c) s)
        (realTData.rightToCoord a b c x r s) :=
  rfl

theorem realT_right_toCoord_leftPure (a b c : ZMod 8)
    (x : (realDData.algebra a).carrier)
    (y : (realDData.algebra b).carrier)
    (z : (realDData.algebra c).carrier)
    (m : realTData.RightCarrier a b c) :
    realTData.rightToCoord a b c
        (realTData.rightRoute.leftPure a b c x y z m) =
      fun targetBC targetABC =>
        CData.rawFinSum (realDData.algebra (a + b + c)) fun sourceBC =>
          CData.rawFinSum (realDData.algebra (a + b + c)) fun sourceABC =>
            (realDData.algebra (a + b + c)).mul
              (rightRouteCoeff realCData a b c targetBC targetABC
                sourceBC sourceABC x y z)
              (realTData.rightToCoord a b c m sourceBC sourceABC) :=
  rfl

theorem realT_right_toCoord_right (a b c : ZMod 8)
    (m : realTData.RightCarrier a b c)
    (q : (realDData.algebra (a + b + c)).carrier) :
    realTData.rightToCoord a b c (realTData.rightRoute.right a b c m q) =
      fun r s => (realDData.algebra (a + b + c)).mul
        (realTData.rightToCoord a b c m r s) q :=
  rfl

/-! ### Rectangular matrix linearity

Connector matrices have different left- and right-frame row types, unlike
the square route-action matrices.  Their table-independent laws use the same
finite-sum argument with separate source and target dimensions. -/

private def realTRectMatrixAction {e : ZMod 8}
    {target₁ target₂ source₁ source₂ : ℕ}
    (K : Fin target₁ → Fin target₂ →
      Fin source₁ → Fin source₂ → Coeff e)
    (x : Fin source₁ → Fin source₂ → Coeff e) :
    Fin target₁ → Fin target₂ → Coeff e :=
  fun targetRow₁ targetRow₂ =>
    CData.rawFinSum (realDData.algebra e) fun sourceRow₁ =>
      CData.rawFinSum (realDData.algebra e) fun sourceRow₂ =>
        Coeff.mul e (K targetRow₁ targetRow₂ sourceRow₁ sourceRow₂)
          (x sourceRow₁ sourceRow₂)

private theorem realTRectMatrixAction_eq_pair_sum {e : ZMod 8}
    {target₁ target₂ source₁ source₂ : ℕ}
    (K : Fin target₁ → Fin target₂ →
      Fin source₁ → Fin source₂ → Coeff e)
    (x : Fin source₁ → Fin source₂ → Coeff e)
    (targetRow₁ : Fin target₁) (targetRow₂ : Fin target₂) :
    realTRectMatrixAction K x targetRow₁ targetRow₂ =
      ∑ source : Fin source₁ × Fin source₂,
        Coeff.mul e (K targetRow₁ targetRow₂ source.1 source.2)
          (x source.1 source.2) := by
  unfold realTRectMatrixAction
  simp_rw [realTRawFinSum_eq_sum]
  exact (Fintype.sum_prod_type' fun sourceRow₁ sourceRow₂ =>
    Coeff.mul e (K targetRow₁ targetRow₂ sourceRow₁ sourceRow₂)
      (x sourceRow₁ sourceRow₂)).symm

/-- Composition of rectangular coefficient matrices.  The connector changes
the two route-row types, so its inverse laws need separate target, middle, and
source dimensions rather than the square route-action lemma above. -/
private theorem realTRectMatrixAction_comp {e : ZMod 8}
    {target₁ target₂ middle₁ middle₂ source₁ source₂ : ℕ}
    (q : ℝ)
    (K : Fin target₁ → Fin target₂ →
      Fin middle₁ → Fin middle₂ → Coeff e)
    (L : Fin middle₁ → Fin middle₂ →
      Fin source₁ → Fin source₂ → Coeff e)
    (M : Fin target₁ → Fin target₂ →
      Fin source₁ → Fin source₂ → Coeff e)
    (x : Fin source₁ → Fin source₂ → Coeff e)
    (hcomp : ∀ targetRow₁ targetRow₂ sourceRow₁ sourceRow₂,
      (∑ middle : Fin middle₁ × Fin middle₂,
        Coeff.mul e
          (K targetRow₁ targetRow₂ middle.1 middle.2)
          (L middle.1 middle.2 sourceRow₁ sourceRow₂)) =
        Coeff.smul e q
          (M targetRow₁ targetRow₂ sourceRow₁ sourceRow₂)) :
    realTRectMatrixAction K (realTRectMatrixAction L x) =
      fun targetRow₁ targetRow₂ =>
        Coeff.smul e q
          (realTRectMatrixAction M x targetRow₁ targetRow₂) := by
  funext targetRow₁ targetRow₂
  simp_rw [realTRectMatrixAction_eq_pair_sum]
  calc
    (∑ middle : Fin middle₁ × Fin middle₂,
        Coeff.mul e (K targetRow₁ targetRow₂ middle.1 middle.2)
          (∑ source : Fin source₁ × Fin source₂,
            Coeff.mul e (L middle.1 middle.2 source.1 source.2)
              (x source.1 source.2))) =
      ∑ middle : Fin middle₁ × Fin middle₂,
        ∑ source : Fin source₁ × Fin source₂,
          Coeff.mul e (K targetRow₁ targetRow₂ middle.1 middle.2)
            (Coeff.mul e (L middle.1 middle.2 source.1 source.2)
              (x source.1 source.2)) := by
        apply Finset.sum_congr rfl
        intro middle _
        exact realTCoeff_mul_sum e _ _
    _ = ∑ source : Fin source₁ × Fin source₂,
        ∑ middle : Fin middle₁ × Fin middle₂,
          Coeff.mul e
            (Coeff.mul e (K targetRow₁ targetRow₂ middle.1 middle.2)
              (L middle.1 middle.2 source.1 source.2))
            (x source.1 source.2) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro source _
        apply Finset.sum_congr rfl
        intro middle _
        exact (Coeff.mul_assoc e _ _ _).symm
    _ = ∑ source : Fin source₁ × Fin source₂,
        Coeff.mul e
          (∑ middle : Fin middle₁ × Fin middle₂,
            Coeff.mul e (K targetRow₁ targetRow₂ middle.1 middle.2)
              (L middle.1 middle.2 source.1 source.2))
          (x source.1 source.2) := by
        apply Finset.sum_congr rfl
        intro source _
        exact (realTCoeff_sum_mul e _ _).symm
    _ = ∑ source : Fin source₁ × Fin source₂,
        Coeff.smul e q
          (Coeff.mul e
            (M targetRow₁ targetRow₂ source.1 source.2)
            (x source.1 source.2)) := by
        apply Finset.sum_congr rfl
        intro source _
        rw [hcomp, Coeff.smul_mul]
    _ = Coeff.smul e q
        (∑ source : Fin source₁ × Fin source₂,
          Coeff.mul e (M targetRow₁ targetRow₂ source.1 source.2)
            (x source.1 source.2)) :=
      (realTCoeff_smul_sum e q _).symm

/-- The rectangular action of the identity kernel is the identity map. -/
private theorem realTRectMatrixAction_one {e : ZMod 8} {n m : ℕ}
    (K : Fin n → Fin m → Fin n → Fin m → Coeff e)
    (x : Fin n → Fin m → Coeff e)
    (hK : ∀ target₁ target₂ source₁ source₂,
      K target₁ target₂ source₁ source₂ =
        if target₁ = source₁ then
          if target₂ = source₂ then Coeff.one e else Coeff.zero e
        else Coeff.zero e) :
    realTRectMatrixAction K x = x := by
  funext target₁ target₂
  rw [realTRectMatrixAction_eq_pair_sum]
  classical
  rw [Fintype.sum_eq_single (target₁, target₂)]
  · rw [hK, if_pos rfl, if_pos rfl, Coeff.one_mul]
  · intro source hsource
    rw [hK]
    by_cases h₁ : target₁ = source.1
    · have h₂ : target₂ ≠ source.2 := by
        intro h₂
        apply hsource
        apply Prod.ext
        · exact h₁.symm
        · exact h₂.symm
      rw [if_pos h₁, if_neg h₂, Coeff.zero_mul]
      rfl
    · rw [if_neg h₁, Coeff.zero_mul]
      rfl

private theorem realTRectMatrixAction_zero {e : ZMod 8}
    {target₁ target₂ source₁ source₂ : ℕ}
    (K : Fin target₁ → Fin target₂ →
      Fin source₁ → Fin source₂ → Coeff e) :
    realTRectMatrixAction K (fun _ _ => Coeff.zero e) =
      fun _ _ => Coeff.zero e := by
  funext targetRow₁ targetRow₂
  rw [realTRectMatrixAction_eq_pair_sum]
  simp_rw [Coeff.mul_zero]
  exact realTCoeff_sum_zero e

private theorem realTRectMatrixAction_add {e : ZMod 8}
    {target₁ target₂ source₁ source₂ : ℕ}
    (K : Fin target₁ → Fin target₂ →
      Fin source₁ → Fin source₂ → Coeff e)
    (x y : Fin source₁ → Fin source₂ → Coeff e) :
    realTRectMatrixAction K (fun sourceRow₁ sourceRow₂ =>
        Coeff.add e (x sourceRow₁ sourceRow₂)
          (y sourceRow₁ sourceRow₂)) =
      fun targetRow₁ targetRow₂ =>
        Coeff.add e
          (realTRectMatrixAction K x targetRow₁ targetRow₂)
          (realTRectMatrixAction K y targetRow₁ targetRow₂) := by
  funext targetRow₁ targetRow₂
  simp_rw [realTRectMatrixAction_eq_pair_sum, Coeff.mul_add]
  exact Finset.sum_add_distrib

private theorem realTRectMatrixAction_neg {e : ZMod 8}
    {target₁ target₂ source₁ source₂ : ℕ}
    (K : Fin target₁ → Fin target₂ →
      Fin source₁ → Fin source₂ → Coeff e)
    (x : Fin source₁ → Fin source₂ → Coeff e) :
    realTRectMatrixAction K (fun sourceRow₁ sourceRow₂ =>
        Coeff.neg e (x sourceRow₁ sourceRow₂)) =
      fun targetRow₁ targetRow₂ =>
        Coeff.neg e (realTRectMatrixAction K x targetRow₁ targetRow₂) := by
  funext targetRow₁ targetRow₂
  simp_rw [realTRectMatrixAction_eq_pair_sum, realTCoeff_mul_neg]
  exact (realTCoeff_neg_sum e _).symm

private theorem realTRectMatrixAction_smul {e : ZMod 8}
    {target₁ target₂ source₁ source₂ : ℕ}
    (q : ℝ)
    (K : Fin target₁ → Fin target₂ →
      Fin source₁ → Fin source₂ → Coeff e)
    (x : Fin source₁ → Fin source₂ → Coeff e) :
    realTRectMatrixAction K (fun sourceRow₁ sourceRow₂ =>
        Coeff.smul e q (x sourceRow₁ sourceRow₂)) =
      fun targetRow₁ targetRow₂ =>
        Coeff.smul e q
          (realTRectMatrixAction K x targetRow₁ targetRow₂) := by
  funext targetRow₁ targetRow₂
  simp_rw [realTRectMatrixAction_eq_pair_sum, Coeff.mul_smul_right]
  exact (realTCoeff_smul_sum e q _).symm

private theorem realTRectMatrixAction_right {e : ZMod 8}
    {target₁ target₂ source₁ source₂ : ℕ}
    (K : Fin target₁ → Fin target₂ →
      Fin source₁ → Fin source₂ → Coeff e)
    (x : Fin source₁ → Fin source₂ → Coeff e) (q : Coeff e) :
    realTRectMatrixAction K
        (fun sourceRow₁ sourceRow₂ =>
          Coeff.mul e (x sourceRow₁ sourceRow₂) q) =
      fun targetRow₁ targetRow₂ =>
        Coeff.mul e (realTRectMatrixAction K x targetRow₁ targetRow₂) q := by
  funext targetRow₁ targetRow₂
  simp_rw [realTRectMatrixAction_eq_pair_sum]
  rw [realTCoeff_sum_mul]
  apply Finset.sum_congr rfl
  intro source _
  exact (Coeff.mul_assoc e _ _ _).symm

/-! ### Raw inverse certificates in the concrete route frames

The certificate layer uses one flat `Fin sigma` frame.  The concrete raw
connector uses a pair of fusion rows on each side.  The following bridges are
value-preserving reindexings; they do not inspect or recompute the frozen
table.
-/

/-- The unscaled inverse numerator in the same concrete row-pair convention
as `realTInverseEntry`. -/
private def realTInverseNumeratorEntry (a b c : ZMod 8)
    (targetAB : realCData.Index a b)
    (targetABC : realCData.Index (a + b) c)
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c)) : Coeff (a + b + c) :=
  fun e =>
    (coeffGet (inverseNumeratorCoeff a b c)
      (realTLeftPosition a b c targetAB targetABC)
      (realTRightPosition a b c sourceBC sourceABC) e.val : Real)

/-- Flattening a concrete left row-pair has the position used by `RealT`. -/
private theorem realTLeftPairEquiv_val (a b c : ZMod 8)
    (r : realCData.Index a b) (s : realCData.Index (a + b) c) :
    (RModCoordinate.ConnectorTableLaws.leftPairEquiv a b c (r, s)).val =
      realTLeftPosition a b c r s := by
  simp [RModCoordinate.ConnectorTableLaws.leftPairEquiv,
    realTLeftPosition]

/-- Flattening a concrete right row-pair has the position used by `RealT`. -/
private theorem realTRightPairEquiv_val (a b c : ZMod 8)
    (r : realCData.Index b c) (s : realCData.Index a (b + c)) :
    (RModCoordinate.ConnectorTableLaws.rightPairEquiv a b c (r, s)).val =
      realTRightPosition a b c r s := by
  simp [RModCoordinate.ConnectorTableLaws.rightPairEquiv,
    realTRightPosition]

/-- The concrete forward entry is the route-pair view of the certified raw
forward coefficient table. -/
private theorem realTForwardEntry_eq_pairCoeff (a b c : ZMod 8)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceAB : realCData.Index a b)
    (sourceABC : realCData.Index (a + b) c) :
    realTForwardEntry a b c targetBC targetABC sourceAB sourceABC =
      RModCoordinate.ConnectorTableLaws.rawForwardPairCoeff a b c
        (targetBC, targetABC) (sourceAB, sourceABC) := by
  funext e
  change
    (coeffGet (forwardCoeff a b c)
        (realTRightPosition a b c targetBC targetABC)
        (realTLeftPosition a b c sourceAB sourceABC) e.val : Real) =
      (coeffGet (forwardCoeff a b c)
        (RModCoordinate.ConnectorTableLaws.rightPairEquiv a b c
          (targetBC, targetABC)).val
        (RModCoordinate.ConnectorTableLaws.leftPairEquiv a b c
          (sourceAB, sourceABC)).val e.val : Real)
  rw [realTRightPairEquiv_val, realTLeftPairEquiv_val]

/-- The concrete unscaled reverse entry is the route-pair view of the
certified inverse numerator. -/
private theorem realTInverseNumeratorEntry_eq_pairCoeff (a b c : ZMod 8)
    (targetAB : realCData.Index a b)
    (targetABC : realCData.Index (a + b) c)
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c)) :
    realTInverseNumeratorEntry a b c targetAB targetABC sourceBC sourceABC =
      RModCoordinate.ConnectorTableLaws.rawInverseNumeratorPairCoeff a b c
        (targetAB, targetABC) (sourceBC, sourceABC) := by
  funext e
  change
    (coeffGet (inverseNumeratorCoeff a b c)
        (realTLeftPosition a b c targetAB targetABC)
        (realTRightPosition a b c sourceBC sourceABC) e.val : Real) =
      (coeffGet (inverseNumeratorCoeff a b c)
        (RModCoordinate.ConnectorTableLaws.leftPairEquiv a b c
          (targetAB, targetABC)).val
        (RModCoordinate.ConnectorTableLaws.rightPairEquiv a b c
          (sourceBC, sourceABC)).val e.val : Real)
  rw [realTLeftPairEquiv_val, realTRightPairEquiv_val]

/-- The executable reverse entry is the exact rational scale applied to the
stored inverse numerator. -/
private theorem realTInverseEntry_eq_smul (a b c : ZMod 8)
    (targetAB : realCData.Index a b)
    (targetABC : realCData.Index (a + b) c)
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c)) :
    realTInverseEntry a b c targetAB targetABC sourceBC sourceABC =
      Coeff.smul (a + b + c) (realTInverseScale a b c)
        (realTInverseNumeratorEntry a b c
          targetAB targetABC sourceBC sourceABC) := by
  rfl

/-! ### Exact scale cancellation

The reciprocal is computed in `Rat` before it is cast to `Real`.  Positivity
of the stored power-of-two scale therefore proves cancellation without a
selected real inverse.
-/

/-- The exact rational reciprocal cancels the stored integral scale. -/
private theorem realTInverseScale_mul_inverseScale (a b c : ZMod 8) :
    realTInverseScale a b c * (inverseScale a b c : Real) = 1 := by
  rw [realTInverseScale]
  norm_num [inverseScale_ne_zero]

/-! ### Scaled pair-sum identities

The unscaled route-pair laws give `lambda I`.  Pulling the exact reciprocal
through `Coeff.mul` and the finite sum turns them into literal identity
kernels on the two concrete route carriers.
-/

/-- Identity coefficient kernel on the right-associated row-pair frame. -/
private def realTRightIdentityKernel (a b c : ZMod 8)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c)) : Coeff (a + b + c) :=
  if (targetBC, targetABC) = (sourceBC, sourceABC) then
    Coeff.one (a + b + c)
  else Coeff.zero (a + b + c)

/-- Identity coefficient kernel on the left-associated row-pair frame. -/
private def realTLeftIdentityKernel (a b c : ZMod 8)
    (targetAB : realCData.Index a b)
    (targetABC : realCData.Index (a + b) c)
    (sourceAB : realCData.Index a b)
    (sourceABC : realCData.Index (a + b) c) : Coeff (a + b + c) :=
  if (targetAB, targetABC) = (sourceAB, sourceABC) then
    Coeff.one (a + b + c)
  else Coeff.zero (a + b + c)

/-- The concrete forward kernel followed by the scaled reverse kernel is the
identity on right-associated row pairs. -/
private theorem realTForwardInverseScaledPairSum (a b c : ZMod 8)
    (targetBC : realCData.Index b c)
    (targetABC : realCData.Index a (b + c))
    (sourceBC : realCData.Index b c)
    (sourceABC : realCData.Index a (b + c)) :
    (∑ middle : realCData.Index a b × realCData.Index (a + b) c,
      Coeff.mul (a + b + c)
        (realTForwardEntry a b c targetBC targetABC middle.1 middle.2)
        (realTInverseEntry a b c middle.1 middle.2 sourceBC sourceABC)) =
      realTRightIdentityKernel a b c
        targetBC targetABC sourceBC sourceABC := by
  calc
    _ = ∑ middle : realCData.Index a b × realCData.Index (a + b) c,
        Coeff.smul (a + b + c) (realTInverseScale a b c)
          (Coeff.mul (a + b + c)
            (RModCoordinate.ConnectorTableLaws.rawForwardPairCoeff a b c
              (targetBC, targetABC) middle)
            (RModCoordinate.ConnectorTableLaws.rawInverseNumeratorPairCoeff
              a b c middle (sourceBC, sourceABC))) := by
          apply Finset.sum_congr rfl
          intro middle _
          rcases middle with ⟨middle₁, middle₂⟩
          rw [realTForwardEntry_eq_pairCoeff, realTInverseEntry_eq_smul,
            realTInverseNumeratorEntry_eq_pairCoeff, Coeff.mul_smul_right]
          rfl
    _ = Coeff.smul (a + b + c) (realTInverseScale a b c)
        (∑ middle : realCData.Index a b × realCData.Index (a + b) c,
          Coeff.mul (a + b + c)
            (RModCoordinate.ConnectorTableLaws.rawForwardPairCoeff a b c
              (targetBC, targetABC) middle)
            (RModCoordinate.ConnectorTableLaws.rawInverseNumeratorPairCoeff
              a b c middle (sourceBC, sourceABC))) :=
      (realTCoeff_smul_sum (a + b + c) (realTInverseScale a b c) _).symm
    _ = Coeff.smul (a + b + c) (realTInverseScale a b c)
        (if (targetBC, targetABC) = (sourceBC, sourceABC) then
          Coeff.smul (a + b + c) (inverseScale a b c : Real)
            (Coeff.one (a + b + c))
        else Coeff.zero (a + b + c)) := by
          exact congrArg
            (Coeff.smul (a + b + c) (realTInverseScale a b c))
            (RModCoordinate.ConnectorTableLaws.rawForwardInversePairSum
              a b c (targetBC, targetABC) (sourceBC, sourceABC))
    _ = realTRightIdentityKernel a b c
        targetBC targetABC sourceBC sourceABC := by
          by_cases hp : (targetBC, targetABC) = (sourceBC, sourceABC)
          · rw [if_pos hp, realTRightIdentityKernel, if_pos hp,
              ← Coeff.mul_smul, realTInverseScale_mul_inverseScale,
              Coeff.one_smul]
          · rw [if_neg hp, realTRightIdentityKernel, if_neg hp,
              Coeff.smul_zero]

/-- The scaled reverse kernel followed by the concrete forward kernel is the
identity on left-associated row pairs. -/
private theorem realTInverseForwardScaledPairSum (a b c : ZMod 8)
    (targetAB : realCData.Index a b)
    (targetABC : realCData.Index (a + b) c)
    (sourceAB : realCData.Index a b)
    (sourceABC : realCData.Index (a + b) c) :
    (∑ middle : realCData.Index b c × realCData.Index a (b + c),
      Coeff.mul (a + b + c)
        (realTInverseEntry a b c targetAB targetABC middle.1 middle.2)
        (realTForwardEntry a b c middle.1 middle.2 sourceAB sourceABC)) =
      realTLeftIdentityKernel a b c
        targetAB targetABC sourceAB sourceABC := by
  calc
    _ = ∑ middle : realCData.Index b c × realCData.Index a (b + c),
        Coeff.smul (a + b + c) (realTInverseScale a b c)
          (Coeff.mul (a + b + c)
            (RModCoordinate.ConnectorTableLaws.rawInverseNumeratorPairCoeff
              a b c (targetAB, targetABC) middle)
            (RModCoordinate.ConnectorTableLaws.rawForwardPairCoeff a b c
              middle (sourceAB, sourceABC))) := by
          apply Finset.sum_congr rfl
          intro middle _
          rcases middle with ⟨middle₁, middle₂⟩
          rw [realTInverseEntry_eq_smul,
            realTInverseNumeratorEntry_eq_pairCoeff,
            realTForwardEntry_eq_pairCoeff, Coeff.smul_mul]
          rfl
    _ = Coeff.smul (a + b + c) (realTInverseScale a b c)
        (∑ middle : realCData.Index b c × realCData.Index a (b + c),
          Coeff.mul (a + b + c)
            (RModCoordinate.ConnectorTableLaws.rawInverseNumeratorPairCoeff
              a b c (targetAB, targetABC) middle)
            (RModCoordinate.ConnectorTableLaws.rawForwardPairCoeff a b c
              middle (sourceAB, sourceABC))) :=
      (realTCoeff_smul_sum (a + b + c) (realTInverseScale a b c) _).symm
    _ = Coeff.smul (a + b + c) (realTInverseScale a b c)
        (if (targetAB, targetABC) = (sourceAB, sourceABC) then
          Coeff.smul (a + b + c) (inverseScale a b c : Real)
            (Coeff.one (a + b + c))
        else Coeff.zero (a + b + c)) := by
          exact congrArg
            (Coeff.smul (a + b + c) (realTInverseScale a b c))
            (RModCoordinate.ConnectorTableLaws.rawInverseForwardPairSum
              a b c (targetAB, targetABC) (sourceAB, sourceABC))
    _ = realTLeftIdentityKernel a b c
        targetAB targetABC sourceAB sourceABC := by
          by_cases hp : (targetAB, targetABC) = (sourceAB, sourceABC)
          · rw [if_pos hp, realTLeftIdentityKernel, if_pos hp,
              ← Coeff.mul_smul, realTInverseScale_mul_inverseScale,
              Coeff.one_smul]
          · rw [if_neg hp, realTLeftIdentityKernel, if_neg hp,
              Coeff.smul_zero]

/-! ### Two-sided inverse laws for the concrete raw connector -/

/-- Applying the forward raw connector after its explicit reverse map is the
identity on the right-associated route. -/
theorem realT_hom_inv_id (a b c : ZMod 8)
    (m : realTData.RightCarrier a b c) :
    realTData.hom a b c (realTData.inv a b c m) = m := by
  change realTRectMatrixAction
    (fun targetBC targetABC sourceAB sourceABC =>
      realTForwardEntry a b c targetBC targetABC sourceAB sourceABC)
    (realTRectMatrixAction
      (fun targetAB targetABC sourceBC sourceABC =>
        realTInverseEntry a b c targetAB targetABC sourceBC sourceABC)
      m) = m
  calc
    _ = fun targetBC targetABC =>
        Coeff.smul (a + b + c) 1
          (realTRectMatrixAction
            (realTRightIdentityKernel a b c) m targetBC targetABC) := by
          apply realTRectMatrixAction_comp
          intro targetBC targetABC sourceBC sourceABC
          rw [Coeff.one_smul]
          exact realTForwardInverseScaledPairSum a b c
            targetBC targetABC sourceBC sourceABC
    _ = realTRectMatrixAction (realTRightIdentityKernel a b c) m := by
          funext targetBC targetABC
          exact Coeff.one_smul (a + b + c) _
    _ = m := by
          apply realTRectMatrixAction_one
          intro targetBC targetABC sourceBC sourceABC
          by_cases hBC : targetBC = sourceBC
          · subst sourceBC
            simp [realTRightIdentityKernel]
          · simp [realTRightIdentityKernel, hBC]

/-- Applying the explicit reverse map after the forward raw connector is the
identity on the left-associated route. -/
theorem realT_inv_hom_id (a b c : ZMod 8)
    (m : realTData.LeftCarrier a b c) :
    realTData.inv a b c (realTData.hom a b c m) = m := by
  change realTRectMatrixAction
    (fun targetAB targetABC sourceBC sourceABC =>
      realTInverseEntry a b c targetAB targetABC sourceBC sourceABC)
    (realTRectMatrixAction
      (fun targetBC targetABC sourceAB sourceABC =>
        realTForwardEntry a b c targetBC targetABC sourceAB sourceABC)
      m) = m
  calc
    _ = fun targetAB targetABC =>
        Coeff.smul (a + b + c) 1
          (realTRectMatrixAction
            (realTLeftIdentityKernel a b c) m targetAB targetABC) := by
          apply realTRectMatrixAction_comp
          intro targetAB targetABC sourceAB sourceABC
          rw [Coeff.one_smul]
          exact realTInverseForwardScaledPairSum a b c
            targetAB targetABC sourceAB sourceABC
    _ = realTRectMatrixAction (realTLeftIdentityKernel a b c) m := by
          funext targetAB targetABC
          exact Coeff.one_smul (a + b + c) _
    _ = m := by
          apply realTRectMatrixAction_one
          intro targetAB targetABC sourceAB sourceABC
          by_cases hAB : targetAB = sourceAB
          · subst sourceAB
            simp [realTLeftIdentityKernel]
          · simp [realTLeftIdentityKernel, hAB]

/-! ### Connector linearity and the endpoint right action

The forward and reverse maps may use different frozen coefficient tables,
but both are rectangular coefficient matrices acting by left multiplication.
Consequently their additive and scalar laws, and commutation with endpoint
right multiplication, do not require any fact about the entries themselves. -/

theorem realT_hom_zero (a b c : ZMod 8) :
    realTData.hom a b c (realTData.leftRoute.zero a b c) =
      realTData.rightRoute.zero a b c := by
  change realTRectMatrixAction
    (fun targetBC targetABC sourceAB sourceABC =>
      realTForwardEntry a b c targetBC targetABC sourceAB sourceABC)
    (fun _ _ => Coeff.zero (a + b + c)) =
      fun _ _ => Coeff.zero (a + b + c)
  exact realTRectMatrixAction_zero _

theorem realT_hom_add (a b c : ZMod 8)
    (x y : realTData.LeftCarrier a b c) :
    realTData.hom a b c (realTData.leftRoute.add a b c x y) =
      realTData.rightRoute.add a b c
        (realTData.hom a b c x) (realTData.hom a b c y) := by
  change realTRectMatrixAction
    (fun targetBC targetABC sourceAB sourceABC =>
      realTForwardEntry a b c targetBC targetABC sourceAB sourceABC)
    (fun sourceAB sourceABC => Coeff.add (a + b + c)
      (x sourceAB sourceABC) (y sourceAB sourceABC)) =
      fun targetBC targetABC => Coeff.add (a + b + c)
        (realTRectMatrixAction
          (fun targetBC targetABC sourceAB sourceABC =>
            realTForwardEntry a b c targetBC targetABC sourceAB sourceABC)
          x targetBC targetABC)
        (realTRectMatrixAction
          (fun targetBC targetABC sourceAB sourceABC =>
            realTForwardEntry a b c targetBC targetABC sourceAB sourceABC)
          y targetBC targetABC)
  exact realTRectMatrixAction_add _ x y

theorem realT_hom_neg (a b c : ZMod 8)
    (x : realTData.LeftCarrier a b c) :
    realTData.hom a b c (realTData.leftRoute.neg a b c x) =
      realTData.rightRoute.neg a b c (realTData.hom a b c x) := by
  change realTRectMatrixAction
    (fun targetBC targetABC sourceAB sourceABC =>
      realTForwardEntry a b c targetBC targetABC sourceAB sourceABC)
    (fun sourceAB sourceABC => Coeff.neg (a + b + c)
      (x sourceAB sourceABC)) = fun targetBC targetABC =>
      Coeff.neg (a + b + c)
        (realTRectMatrixAction
          (fun targetBC targetABC sourceAB sourceABC =>
            realTForwardEntry a b c targetBC targetABC sourceAB sourceABC)
          x targetBC targetABC)
  exact realTRectMatrixAction_neg _ x

theorem realT_hom_smul (a b c : ZMod 8) (q : ℝ)
    (x : realTData.LeftCarrier a b c) :
    realTData.hom a b c (realTData.leftRoute.smul a b c q x) =
      realTData.rightRoute.smul a b c q (realTData.hom a b c x) := by
  change realTRectMatrixAction
    (fun targetBC targetABC sourceAB sourceABC =>
      realTForwardEntry a b c targetBC targetABC sourceAB sourceABC)
    (fun sourceAB sourceABC => Coeff.smul (a + b + c) q
      (x sourceAB sourceABC)) = fun targetBC targetABC =>
      Coeff.smul (a + b + c) q
        (realTRectMatrixAction
          (fun targetBC targetABC sourceAB sourceABC =>
            realTForwardEntry a b c targetBC targetABC sourceAB sourceABC)
          x targetBC targetABC)
  exact realTRectMatrixAction_smul q _ x

theorem realT_inv_zero (a b c : ZMod 8) :
    realTData.inv a b c (realTData.rightRoute.zero a b c) =
      realTData.leftRoute.zero a b c := by
  change realTRectMatrixAction
    (fun targetAB targetABC sourceBC sourceABC =>
      realTInverseEntry a b c targetAB targetABC sourceBC sourceABC)
    (fun _ _ => Coeff.zero (a + b + c)) =
      fun _ _ => Coeff.zero (a + b + c)
  exact realTRectMatrixAction_zero _

theorem realT_inv_add (a b c : ZMod 8)
    (x y : realTData.RightCarrier a b c) :
    realTData.inv a b c (realTData.rightRoute.add a b c x y) =
      realTData.leftRoute.add a b c
        (realTData.inv a b c x) (realTData.inv a b c y) := by
  change realTRectMatrixAction
    (fun targetAB targetABC sourceBC sourceABC =>
      realTInverseEntry a b c targetAB targetABC sourceBC sourceABC)
    (fun sourceBC sourceABC => Coeff.add (a + b + c)
      (x sourceBC sourceABC) (y sourceBC sourceABC)) =
      fun targetAB targetABC => Coeff.add (a + b + c)
        (realTRectMatrixAction
          (fun targetAB targetABC sourceBC sourceABC =>
            realTInverseEntry a b c targetAB targetABC sourceBC sourceABC)
          x targetAB targetABC)
        (realTRectMatrixAction
          (fun targetAB targetABC sourceBC sourceABC =>
            realTInverseEntry a b c targetAB targetABC sourceBC sourceABC)
          y targetAB targetABC)
  exact realTRectMatrixAction_add _ x y

theorem realT_inv_neg (a b c : ZMod 8)
    (x : realTData.RightCarrier a b c) :
    realTData.inv a b c (realTData.rightRoute.neg a b c x) =
      realTData.leftRoute.neg a b c (realTData.inv a b c x) := by
  change realTRectMatrixAction
    (fun targetAB targetABC sourceBC sourceABC =>
      realTInverseEntry a b c targetAB targetABC sourceBC sourceABC)
    (fun sourceBC sourceABC => Coeff.neg (a + b + c)
      (x sourceBC sourceABC)) = fun targetAB targetABC =>
      Coeff.neg (a + b + c)
        (realTRectMatrixAction
          (fun targetAB targetABC sourceBC sourceABC =>
            realTInverseEntry a b c targetAB targetABC sourceBC sourceABC)
          x targetAB targetABC)
  exact realTRectMatrixAction_neg _ x

theorem realT_inv_smul (a b c : ZMod 8) (q : ℝ)
    (x : realTData.RightCarrier a b c) :
    realTData.inv a b c (realTData.rightRoute.smul a b c q x) =
      realTData.leftRoute.smul a b c q (realTData.inv a b c x) := by
  change realTRectMatrixAction
    (fun targetAB targetABC sourceBC sourceABC =>
      realTInverseEntry a b c targetAB targetABC sourceBC sourceABC)
    (fun sourceBC sourceABC => Coeff.smul (a + b + c) q
      (x sourceBC sourceABC)) = fun targetAB targetABC =>
      Coeff.smul (a + b + c) q
        (realTRectMatrixAction
          (fun targetAB targetABC sourceBC sourceABC =>
            realTInverseEntry a b c targetAB targetABC sourceBC sourceABC)
          x targetAB targetABC)
  exact realTRectMatrixAction_smul q _ x

theorem realT_hom_right (a b c : ZMod 8)
    (m : realTData.LeftCarrier a b c)
    (q : (realDData.algebra (a + b + c)).carrier) :
    realTData.hom a b c (realTData.leftRoute.right a b c m q) =
      realTData.rightRoute.right a b c (realTData.hom a b c m) q := by
  change realTRectMatrixAction
    (fun targetBC targetABC sourceAB sourceABC =>
      realTForwardEntry a b c targetBC targetABC sourceAB sourceABC)
    (fun sourceAB sourceABC => Coeff.mul (a + b + c)
      (m sourceAB sourceABC) q) = fun targetBC targetABC =>
      Coeff.mul (a + b + c)
        (realTRectMatrixAction
          (fun targetBC targetABC sourceAB sourceABC =>
            realTForwardEntry a b c targetBC targetABC sourceAB sourceABC)
          m targetBC targetABC) q
  exact realTRectMatrixAction_right _ m q

theorem realT_inv_right (a b c : ZMod 8)
    (m : realTData.RightCarrier a b c)
    (q : (realDData.algebra (a + b + c)).carrier) :
    realTData.inv a b c (realTData.rightRoute.right a b c m q) =
      realTData.leftRoute.right a b c (realTData.inv a b c m) q := by
  change realTRectMatrixAction
    (fun targetAB targetABC sourceBC sourceABC =>
      realTInverseEntry a b c targetAB targetABC sourceBC sourceABC)
    (fun sourceBC sourceABC => Coeff.mul (a + b + c)
      (m sourceBC sourceABC) q) = fun targetAB targetABC =>
      Coeff.mul (a + b + c)
        (realTRectMatrixAction
          (fun targetAB targetABC sourceBC sourceABC =>
            realTInverseEntry a b c targetAB targetABC sourceBC sourceABC)
          m targetAB targetABC) q
  exact realTRectMatrixAction_right _ m q

/-! ## Proof-only semantic realization of the forward connector

The executable connector above stays entirely in raw coordinates.  For its
remaining grading and left-action laws, the following private columns place
those coordinates in the semantic left and right route frames.  They select
no data: both are obtained by the canonical frame equivalences and the
already-defined coefficient realization. -/

/-- The coefficient realization, with its carrier ascribed in the exact
spelling used by the gauge module instances. -/
private noncomputable def realTSemanticCoeff (a : ZMod 8) (x : Coeff a) :
    (realGauge.D a).carrier :=
  Coeff.semantic a x

private theorem realTSemanticCoeff_sum {I : Type*} [Fintype I]
    (a : ZMod 8) (f : I → Coeff a) :
    realTSemanticCoeff a (∑ i, f i) =
      ∑ i, realTSemanticCoeff a (f i) := by
  change Coeff.semantic a (∑ i, f i) = ∑ i, Coeff.semantic a (f i)
  exact map_sum (Coeff.semantic a) f Finset.univ

private theorem realTSemanticCoeff_mul (a : ZMod 8) (x y : Coeff a) :
    realTSemanticCoeff a (Coeff.mul a x y) =
      realTSemanticCoeff a x * realTSemanticCoeff a y := by
  change Coeff.semantic a (Coeff.mul a x y) =
    Coeff.semantic a x * Coeff.semantic a y
  exact Coeff.semantic_mul a x y

private theorem realTSemanticCoeff_smul (a : ZMod 8) (q : ℝ)
    (x : Coeff a) :
    realTSemanticCoeff a (Coeff.smul a q x) =
      q • realTSemanticCoeff a x := by
  change Coeff.semantic a (Coeff.smul a q x) = q • Coeff.semantic a x
  exact Coeff.semantic_smul a q x

/-- A raw left-route coordinate vector, read in the semantic composite
left frame. -/
private noncomputable def realTLeftSemanticColumn (a b c : ZMod 8)
    (m : FusionTable.Index a b → FusionTable.Index (a + b) c → Coeff (a + b + c)) :
    Bimod.FusionColumn (realGauge.gaugeRouteL a b c) :=
  fun I =>
    let p := (GaugeChi.gblIndexEquiv ℝ realGauge a b c).symm I
    realTSemanticCoeff (a + b + c)
      (m (finSumFinEquiv p.1) (finSumFinEquiv p.2))

/-- A raw right-route coordinate vector, read in the semantic native right
frame.  Its coefficients are transported across endpoint associativity. -/
private noncomputable def realTRightSemanticColumn (a b c : ZMod 8)
    (m : FusionTable.Index b c → FusionTable.Index a (b + c) → Coeff (a + b + c)) :
    Bimod.FusionColumn (realGauge.gaugeRouteR a b c) :=
  fun I =>
    let p := (GaugeChi.gbrNativeIndexEquiv ℝ realGauge a b c).symm I
    (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
      (realTSemanticCoeff (a + b + c)
        (m (finSumFinEquiv p.1) (finSumFinEquiv p.2)))

/-- The corresponding element of the semantic left route. -/
private noncomputable def realTLeftSemantic (a b c : ZMod 8)
    (m : FusionTable.Index a b → FusionTable.Index (a + b) c → Coeff (a + b + c)) : GaugeChi.GBL realGauge a b c :=
  (GaugeChi.gblColumnEquiv ℝ realGauge a b c).symm
    (realTLeftSemanticColumn a b c m)

/-- The corresponding element of the semantic right route. -/
private noncomputable def realTRightSemantic (a b c : ZMod 8)
    (m : FusionTable.Index b c → FusionTable.Index a (b + c) → Coeff (a + b + c)) : GaugeChi.GBR realGauge a b c :=
  (GaugeChi.gbrNativeColumnEquiv ℝ realGauge a b c).symm
    (realTRightSemanticColumn a b c m)

/-- Reindex a raw left row pair directly into the semantic composite frame. -/
private noncomputable def realTLeftPairSemanticEquiv (a b c : ZMod 8) :
    (FusionTable.Index a b × FusionTable.Index (a + b) c) ≃
      (Fin (realGauge.gaugeSizeL a b c).1 ⊕
        Fin (realGauge.gaugeSizeL a b c).2) :=
  ((finSumFinEquiv.symm.prodCongr finSumFinEquiv.symm).trans
    (GaugeChi.gblIndexEquiv ℝ realGauge a b c))

/-- Reindex a raw right row pair directly into the semantic native frame. -/
private noncomputable def realTRightPairSemanticEquiv (a b c : ZMod 8) :
    (FusionTable.Index b c × FusionTable.Index a (b + c)) ≃
      (Fin (realGauge.gaugeSizeR a b c).1 ⊕
        Fin (realGauge.gaugeSizeR a b c).2) :=
  ((finSumFinEquiv.symm.prodCongr finSumFinEquiv.symm).trans
    (GaugeChi.gbrNativeIndexEquiv ℝ realGauge a b c))

@[simp]
private theorem realTLeftPairSemanticEquiv_apply (a b c : ZMod 8)
    (r : FusionTable.Index a b) (s : FusionTable.Index (a + b) c) :
    realTLeftPairSemanticEquiv a b c (r, s) =
      GaugeChi.gblIndexEquiv ℝ realGauge a b c
        (FusionTable.frameIndex a b r,
          FusionTable.frameIndex (a + b) c s) :=
  rfl

@[simp]
private theorem realTRightPairSemanticEquiv_apply (a b c : ZMod 8)
    (r : FusionTable.Index b c) (s : FusionTable.Index a (b + c)) :
    realTRightPairSemanticEquiv a b c (r, s) =
      GaugeChi.gbrNativeIndexEquiv ℝ realGauge a b c
        (FusionTable.frameIndex b c r,
          FusionTable.frameIndex a (b + c) s) :=
  rfl

@[simp]
private theorem realTLeftPairSemanticEquiv_symm_apply (a b c : ZMod 8)
    (r : FusionTable.Index a b) (s : FusionTable.Index (a + b) c) :
    (GaugeChi.gblIndexEquiv ℝ realGauge a b c).symm
        (realTLeftPairSemanticEquiv a b c (r, s)) =
      (FusionTable.frameIndex a b r,
        FusionTable.frameIndex (a + b) c s) := by
  rw [realTLeftPairSemanticEquiv_apply,
    (GaugeChi.gblIndexEquiv ℝ realGauge a b c).symm_apply_apply]
  rfl

@[simp]
private theorem realTRightPairSemanticEquiv_symm_apply (a b c : ZMod 8)
    (r : FusionTable.Index b c) (s : FusionTable.Index a (b + c)) :
    (GaugeChi.gbrNativeIndexEquiv ℝ realGauge a b c).symm
        (realTRightPairSemanticEquiv a b c (r, s)) =
      (FusionTable.frameIndex b c r,
        FusionTable.frameIndex a (b + c) s) := by
  rw [realTRightPairSemanticEquiv_apply,
    (GaugeChi.gbrNativeIndexEquiv ℝ realGauge a b c).symm_apply_apply]
  rfl

@[simp]
private theorem realTLeftSemanticColumn_apply_pair (a b c : ZMod 8)
    (m : FusionTable.Index a b → FusionTable.Index (a + b) c → Coeff (a + b + c))
    (r : FusionTable.Index a b) (s : FusionTable.Index (a + b) c) :
    realTLeftSemanticColumn a b c m
        (GaugeChi.gblIndexEquiv ℝ realGauge a b c
          (FusionTable.frameIndex a b r,
            FusionTable.frameIndex (a + b) c s)) =
      realTSemanticCoeff (a + b + c) (m r s) := by
  change realTSemanticCoeff (a + b + c)
      (m
        (finSumFinEquiv
          ((GaugeChi.gblIndexEquiv ℝ realGauge a b c).symm
            (realTLeftPairSemanticEquiv a b c (r, s))).1)
        (finSumFinEquiv
          ((GaugeChi.gblIndexEquiv ℝ realGauge a b c).symm
            (realTLeftPairSemanticEquiv a b c (r, s))).2)) = _
  rw [realTLeftPairSemanticEquiv_symm_apply]
  simp [FusionTable.frameIndex]

@[simp]
private theorem realTRightSemanticColumn_apply_pair (a b c : ZMod 8)
    (m : FusionTable.Index b c → FusionTable.Index a (b + c) → Coeff (a + b + c))
    (r : FusionTable.Index b c) (s : FusionTable.Index a (b + c)) :
    realTRightSemanticColumn a b c m
        (GaugeChi.gbrNativeIndexEquiv ℝ realGauge a b c
          (FusionTable.frameIndex b c r,
            FusionTable.frameIndex a (b + c) s)) =
      (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
        (realTSemanticCoeff (a + b + c) (m r s)) := by
  change (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
      (realTSemanticCoeff (a + b + c)
        (m
          (finSumFinEquiv
            ((GaugeChi.gbrNativeIndexEquiv ℝ realGauge a b c).symm
              (realTRightPairSemanticEquiv a b c (r, s))).1)
          (finSumFinEquiv
            ((GaugeChi.gbrNativeIndexEquiv ℝ realGauge a b c).symm
              (realTRightPairSemanticEquiv a b c (r, s))).2))) = _
  rw [realTRightPairSemanticEquiv_symm_apply]
  simp [FusionTable.frameIndex]

@[simp]
private theorem realTLeftSemanticColumn_apply_semanticPair
    (a b c : ZMod 8)
    (m : FusionTable.Index a b →
      FusionTable.Index (a + b) c → Coeff (a + b + c))
    (r : FusionTable.Index a b) (s : FusionTable.Index (a + b) c) :
    realTLeftSemanticColumn a b c m
        (realTLeftPairSemanticEquiv a b c (r, s)) =
      realTSemanticCoeff (a + b + c) (m r s) := by
  rw [realTLeftPairSemanticEquiv_apply,
    realTLeftSemanticColumn_apply_pair]

@[simp]
private theorem realTRightSemanticColumn_apply_semanticPair
    (a b c : ZMod 8)
    (m : FusionTable.Index b c →
      FusionTable.Index a (b + c) → Coeff (a + b + c))
    (r : FusionTable.Index b c) (s : FusionTable.Index a (b + c)) :
    realTRightSemanticColumn a b c m
        (realTRightPairSemanticEquiv a b c (r, s)) =
      (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
        (realTSemanticCoeff (a + b + c) (m r s)) := by
  rw [realTRightPairSemanticEquiv_apply,
    realTRightSemanticColumn_apply_pair]

@[simp]
private theorem realTLeftSemantic_toColumn (a b c : ZMod 8)
    (m : FusionTable.Index a b → FusionTable.Index (a + b) c → Coeff (a + b + c)) :
    GaugeChi.gblColumnEquiv ℝ realGauge a b c
        (realTLeftSemantic a b c m) = realTLeftSemanticColumn a b c m :=
  (GaugeChi.gblColumnEquiv ℝ realGauge a b c).apply_symm_apply _

@[simp]
private theorem realTRightSemantic_toColumn (a b c : ZMod 8)
    (m : FusionTable.Index b c → FusionTable.Index a (b + c) → Coeff (a + b + c)) :
    GaugeChi.gbrNativeColumnEquiv ℝ realGauge a b c
        (realTRightSemantic a b c m) = realTRightSemanticColumn a b c m :=
  (GaugeChi.gbrNativeColumnEquiv ℝ realGauge a b c).apply_symm_apply _

/- The computable pair flattening and the semantic composite-frame
flattening are the same standard equivalence, viewed before and after the
individual `Fin (p + q)` indices are split. -/

private theorem realTSumPos_frameEquiv {p q sigma : ℕ}
    (h : p + q = sigma) (u : Fin p ⊕ Fin q) :
    GaugeChi.sumPos u = (Superfusion.frameEquiv h u).val := by
  rcases u with u | u <;> rfl

private theorem realTLeftSemanticFrame_val (a b c : ZMod 8)
    (r : FusionTable.Index a b) (s : FusionTable.Index (a + b) c) :
    (RModCoordinate.RawSemanticConnector.leftFrameEquiv a b c
      (GaugeChi.gblIndexEquiv ℝ realGauge a b c
        (FusionTable.frameIndex a b r,
          FusionTable.frameIndex (a + b) c s))).val =
      realTLeftPosition a b c r s := by
  rfl

private theorem realTRightSemanticFrame_val (a b c : ZMod 8)
    (r : FusionTable.Index b c) (s : FusionTable.Index a (b + c)) :
    (RModCoordinate.RawSemanticConnector.rightFrameEquiv a b c
      (GaugeChi.gbrNativeIndexEquiv ℝ realGauge a b c
        (FusionTable.frameIndex b c r,
          FusionTable.frameIndex a (b + c) s))).val =
      realTRightPosition a b c r s := by
  rfl

private theorem realTLeftSemanticFrame_sumPos (a b c : ZMod 8)
    (r : FusionTable.Index a b) (s : FusionTable.Index (a + b) c) :
    GaugeChi.sumPos
        (GaugeChi.gblIndexEquiv ℝ realGauge a b c
          (FusionTable.frameIndex a b r,
            FusionTable.frameIndex (a + b) c s)) =
      realTLeftPosition a b c r s := by
  let I := GaugeChi.gblIndexEquiv ℝ realGauge a b c
    (FusionTable.frameIndex a b r,
      FusionTable.frameIndex (a + b) c s)
  calc
    GaugeChi.sumPos I =
        (RModCoordinate.RawSemanticConnector.leftFrameEquiv a b c I).val :=
      realTSumPos_frameEquiv
        (RModCoordinate.RawSemanticConnector.leftTotal_eq_sigma a b c) I
    _ = realTLeftPosition a b c r s :=
      realTLeftSemanticFrame_val a b c r s

private theorem realTRightSemanticFrame_sumPos (a b c : ZMod 8)
    (r : FusionTable.Index b c) (s : FusionTable.Index a (b + c)) :
    GaugeChi.sumPos
        (GaugeChi.gbrNativeIndexEquiv ℝ realGauge a b c
          (FusionTable.frameIndex b c r,
            FusionTable.frameIndex a (b + c) s)) =
      realTRightPosition a b c r s := by
  let I := GaugeChi.gbrNativeIndexEquiv ℝ realGauge a b c
    (FusionTable.frameIndex b c r,
      FusionTable.frameIndex a (b + c) s)
  calc
    GaugeChi.sumPos I =
        (RModCoordinate.RawSemanticConnector.rightFrameEquiv a b c I).val :=
      realTSumPos_frameEquiv
        (RModCoordinate.RawSemanticConnector.rightTotal_eq_sigma a b c) I
    _ = realTRightPosition a b c r s :=
      realTRightSemanticFrame_val a b c r s

/- Coefficient realization commutes with equality transport between endpoint
algebras. -/

private theorem realTCoeffSemantic_cast {u v : ZMod 8} (h : u = v)
    (x : Coeff u) :
    realTSemanticCoeff v (realCoeffCast h x) =
      (realGauge.gaugeCast h).toAlgEquiv (realTSemanticCoeff u x) := by
  subst v
  rfl

/- For associativity, this transport is the corresponding reindexing of the
canonical finite basis expansion. -/

private theorem realTCoeffSemantic_gaugeCast (a b c : ZMod 8)
    (x : Coeff (a + b + c)) :
    (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
        (realTSemanticCoeff (a + b + c) x) =
      ∑ g : Fin (realRepDim (a + (b + c)).val),
        x ((finCongr (congrArg (fun z : ZMod 8 => realRepDim z.val)
          (_root_.add_assoc a b c))).symm g) •
          realRepBasis (a + (b + c)) g := by
  rw [← realTCoeffSemantic_cast (_root_.add_assoc a b c) x]
  change Coeff.semantic (a + (b + c))
      (realCoeffCast (_root_.add_assoc a b c) x) = _
  simp only [Coeff.semantic, Module.Basis.equivFun_symm_apply,
    realCoeffCast_apply]

/-- The outer native endpoint cast cancels the coordinate route's inverse
associativity cast. -/
private theorem realTCoeffSemantic_rightCast_cancel (a b c : ZMod 8)
    (x : Coeff (a + (b + c))) :
    (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
        (realTSemanticCoeff (a + b + c)
          (realCoeffCast (_root_.add_assoc a b c).symm x)) =
      realTSemanticCoeff (a + (b + c)) x := by
  rw [realTCoeffSemantic_cast,
    ← realGauge.gaugeCast_symm_apply (_root_.add_assoc a b c)]
  exact (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv.apply_symm_apply _

/-- Each executable forward coefficient is exactly the corresponding entry
of the already-certified native semantic connector matrix. -/
private theorem realTForwardEntry_semantic (a b c : ZMod 8)
    (targetBC : FusionTable.Index b c)
    (targetABC : FusionTable.Index a (b + c))
    (sourceAB : FusionTable.Index a b)
    (sourceABC : FusionTable.Index (a + b) c) :
    (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
        (realTSemanticCoeff (a + b + c)
          (realTForwardEntry a b c targetBC targetABC sourceAB sourceABC)) =
      RModCoordinate.RawSemanticConnector.forwardMatrix a b c
        (GaugeChi.gbrNativeIndexEquiv ℝ realGauge a b c
          (FusionTable.frameIndex b c targetBC,
            FusionTable.frameIndex a (b + c) targetABC))
        (GaugeChi.gblIndexEquiv ℝ realGauge a b c
          (FusionTable.frameIndex a b sourceAB,
            FusionTable.frameIndex (a + b) c sourceABC)) := by
  classical
  rw [realTCoeffSemantic_gaugeCast,
    RModCoordinate.RawSemanticSkeletalData.forwardMatrix_eq_native_raw,
    Superfusion.matOfCoeff₂_apply]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  simp only [realTForwardEntry]
  rw [realTRightSemanticFrame_sumPos, realTLeftSemanticFrame_sumPos]
  rfl

/-- The executable forward matrix action is the semantic native connector
action after the two canonical column identifications. -/
private theorem realTHom_semanticColumn (a b c : ZMod 8)
    (m : FusionTable.Index a b → FusionTable.Index (a + b) c → Coeff (a + b + c)) :
    realTRightSemanticColumn a b c (realTHom a b c m) =
      GaugeChi.gmulVecMapNative ℝ realGauge a b c
        (RModCoordinate.RawSemanticConnector.forwardMatrix a b c)
        (realTLeftSemanticColumn a b c m) := by
  classical
  funext I
  obtain ⟨target, rfl⟩ := (realTRightPairSemanticEquiv a b c).surjective I
  rcases target with ⟨targetBC, targetABC⟩
  rw [realTRightSemanticColumn_apply_semanticPair,
    GaugeChi.gmulVecMapNative_apply]
  change
    (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
        (realTSemanticCoeff (a + b + c)
          (realTHom a b c m targetBC targetABC)) =
      ∑ J,
        RModCoordinate.RawSemanticConnector.forwardMatrix a b c
            (realTRightPairSemanticEquiv a b c (targetBC, targetABC)) J *
          (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
            (realTLeftSemanticColumn a b c m J)
  unfold realTHom
  rw [realTRawFinSum_eq_sum]
  simp_rw [realTRawFinSum_eq_sum, realTSemanticCoeff_sum,
    realTSemanticCoeff_mul, map_sum, map_mul]
  conv_rhs =>
    rw [← Equiv.sum_comp (realTLeftPairSemanticEquiv a b c)
      (fun J =>
        RModCoordinate.RawSemanticConnector.forwardMatrix a b c
            (realTRightPairSemanticEquiv a b c (targetBC, targetABC)) J *
          (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
            (realTLeftSemanticColumn a b c m J)),
      Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro sourceAB _
  apply Finset.sum_congr rfl
  intro sourceABC _
  rw [realTForwardEntry_semantic,
    realTLeftSemanticColumn_apply_semanticPair]
  rw [realTRightPairSemanticEquiv_apply,
    realTLeftPairSemanticEquiv_apply]

/-- Element-level form of the forward semantic conjugacy. -/
private theorem realTHom_semantic (a b c : ZMod 8)
    (m : FusionTable.Index a b → FusionTable.Index (a + b) c → Coeff (a + b + c)) :
    realTRightSemantic a b c (realTHom a b c m) =
      GaugeChi.gtOfTNative ℝ realGauge a b c
        (RModCoordinate.RawSemanticConnector.forwardMatrix a b c)
        (realTLeftSemantic a b c m) := by
  apply (GaugeChi.gbrNativeColumnEquiv ℝ realGauge a b c).injective
  rw [realTRightSemantic_toColumn, GaugeChi.gtOfTNative_apply,
    (GaugeChi.gbrNativeColumnEquiv ℝ realGauge a b c).apply_symm_apply,
    realTLeftSemantic_toColumn, realTHom_semanticColumn]

/-! ### Coordinate grading versus semantic column grading -/

/-- Coordinate support gives semantic homogeneity in the canonical basis. -/
private theorem realTCoeffSemantic_mem_of_memGrade (a : ZMod 8)
    (d : ZMod 2) (x : Coeff a) (hx : Coeff.MemGrade a d x) :
    Coeff.semantic a x ∈ (realRep a).grading d := by
  classical
  simp only [Coeff.semantic, Module.Basis.equivFun_symm_apply]
  apply Submodule.sum_mem
  intro g _
  by_cases hg : realRepBasisParity a g = d
  · exact Submodule.smul_mem _ _ (hg ▸ realRepBasis_mem a g)
  · rw [hx g hg, zero_smul]
    exact Submodule.zero_mem _

private theorem realTSemanticCoeff_mem_of_memGrade (a : ZMod 8)
    (d : ZMod 2) (x : Coeff a) (hx : Coeff.MemGrade a d x) :
    realTSemanticCoeff a x ∈ (realGauge.D a).grading d := by
  change Coeff.semantic a x ∈ (realRep a).grading d
  exact realTCoeffSemantic_mem_of_memGrade a d x hx

private theorem realTZMod2_eq_add_one_of_ne (p d : ZMod 2) (h : p ≠ d) :
    p = d + 1 := by
  rcases zmod2_cases p with hp | hp <;>
    rcases zmod2_cases d with hd | hd <;>
    subst p <;> subst d <;> simp_all [Coeff.add_self_eq_zero]

/-- The canonical homogeneous basis also detects coordinate support. -/
private theorem realTCoeffSemantic_mem_iff_memGrade (a : ZMod 8)
    (d : ZMod 2) (x : Coeff a) :
    Coeff.semantic a x ∈ (realRep a).grading d ↔
      Coeff.MemGrade a d x := by
  constructor
  · intro hx
    let xd : Coeff a := Coeff.component a d x
    let xo : Coeff a := Coeff.component a (d + 1) x
    have hxd : Coeff.semantic a xd ∈ (realRep a).grading d :=
      realTCoeffSemantic_mem_of_memGrade a d xd
        (Coeff.component_memGrade a d x)
    have hxo' : Coeff.semantic a xo ∈ (realRep a).grading (d + 1) :=
      realTCoeffSemantic_mem_of_memGrade a (d + 1) xo
        (Coeff.component_memGrade a (d + 1) x)
    have hsplit : Coeff.add a xd xo = x :=
      Coeff.component_complement a d x
    have hsem : Coeff.semantic a xd + Coeff.semantic a xo =
        Coeff.semantic a x := by
      rw [← Coeff.semantic_add, hsplit]
    have hxo : Coeff.semantic a xo ∈ (realRep a).grading d := by
      have heq : Coeff.semantic a xo =
          Coeff.semantic a x - Coeff.semantic a xd := by
        rw [← hsem]
        abel
      rw [heq]
      exact Submodule.sub_mem _ hx hxd
    have hzero : Coeff.semantic a xo = 0 := by
      rcases zmod2_cases d with hd | hd <;> subst d
      · exact (isCompl_grades (realRep a).grading).disjoint.le_bot
          ⟨hxo, hxo'⟩
      · exact (isCompl_grades (realRep a).grading).disjoint.symm.le_bot
          ⟨hxo, hxo'⟩
    have hxo0 : xo = Coeff.zero a := by
      apply (Coeff.semantic a).injective
      rw [hzero, Coeff.semantic_zero]
    intro g hg
    have hp : realRepBasisParity a g = d + 1 :=
      realTZMod2_eq_add_one_of_ne _ _ hg
    have hcoord := congrFun hxo0 g
    simpa [xo, Coeff.component, hp, Coeff.zero] using hcoord
  · exact realTCoeffSemantic_mem_of_memGrade a d x

private theorem realTSemanticCoeff_mem_iff_memGrade (a : ZMod 8)
    (d : ZMod 2) (x : Coeff a) :
    realTSemanticCoeff a x ∈ (realGauge.D a).grading d ↔
      Coeff.MemGrade a d x := by
  change Coeff.semantic a x ∈ (realRep a).grading d ↔
    Coeff.MemGrade a d x
  exact realTCoeffSemantic_mem_iff_memGrade a d x

/-- The raw even-first row parity is the semantic sum-frame parity. -/
private theorem realTIndexParity_eq_sumParity (a b : ZMod 8)
    (r : FusionTable.Index a b) :
    FusionTable.indexParity a b r =
      sumParity (realSize a b).1 (realSize a b).2
        (FusionTable.frameIndex a b r) := by
  rcases hframe : FusionTable.frameIndex a b r with u | u
  · have hr : r = finSumFinEquiv (Sum.inl u) := by
      calc
        r = finSumFinEquiv (FusionTable.frameIndex a b r) :=
          (finSumFinEquiv.apply_symm_apply r).symm
        _ = finSumFinEquiv (Sum.inl u) := congrArg finSumFinEquiv hframe
    rw [hr]
    simp [FusionTable.indexParity, sumParity]
  · have hr : r = finSumFinEquiv (Sum.inr u) := by
      calc
        r = finSumFinEquiv (FusionTable.frameIndex a b r) :=
          (finSumFinEquiv.apply_symm_apply r).symm
        _ = finSumFinEquiv (Sum.inr u) := congrArg finSumFinEquiv hframe
    rw [hr]
    simp [FusionTable.indexParity, sumParity]

/-- Homogeneity of raw left-route coordinates becomes homogeneity in the
semantic left route. -/
private theorem realTLeftSemantic_mem_grading (a b c : ZMod 8)
    (i : ZMod 2) (m : FusionTable.Index a b → FusionTable.Index (a + b) c → Coeff (a + b + c))
    (hm : realLeftRouteData.MemGrade a b c i m) :
    realTLeftSemantic a b c m ∈ GaugeChi.GBL.grading realGauge a b c i := by
  apply (GaugeChi.gblColumnEquiv_mem_grading_iff
    ℝ realGauge a b c).mp
  rw [realTLeftSemantic_toColumn]
  intro I
  obtain ⟨p, rfl⟩ := (realTLeftPairSemanticEquiv a b c).surjective I
  rcases p with ⟨r, s⟩
  rw [realTLeftSemanticColumn_apply_semanticPair]
  have hcoord := congrFun (congrFun hm r) s
  have hgrade : Coeff.MemGrade (a + b + c)
      (i + FusionTable.indexParity a b r +
        FusionTable.indexParity (a + b) c s) (m r s) :=
    (Coeff.component_eq_self_iff (a + b + c)
      (i + FusionTable.indexParity a b r +
        FusionTable.indexParity (a + b) c s) (m r s)).1 hcoord
  have hpar := GaugeChi.gblIndexEquiv_parity ℝ realGauge a b c
    (FusionTable.frameIndex a b r, FusionTable.frameIndex (a + b) c s)
  rw [← realTLeftPairSemanticEquiv_apply a b c r s] at hpar
  rw [← hpar]
  apply (realTSemanticCoeff_mem_iff_memGrade (a + b + c) _ _).2
  simpa only [realGauge_size, realTIndexParity_eq_sumParity,
    add_assoc] using hgrade

/-- Conversely, semantic homogeneity of a native right-route element is
detected by its raw coordinate projections. -/
private theorem realTRight_memGrade_of_semantic (a b c : ZMod 8)
    (i : ZMod 2) (m : FusionTable.Index b c → FusionTable.Index a (b + c) → Coeff (a + b + c))
    (hm : realTRightSemantic a b c m ∈
      GaugeChi.GBR.grading realGauge a b c i) :
    realRightRouteData.MemGrade a b c i m := by
  have hcolumn : realTRightSemanticColumn a b c m ∈
      Bimod.FusionColumn.grading (realGauge.gaugeRouteR a b c) i := by
    have h := (GaugeChi.gbrNativeColumnEquiv_mem_grading_iff
      ℝ realGauge a b c).2 hm
    simpa only [realTRightSemantic_toColumn] using h
  funext r s
  change FusionTable.Index b c at r
  change FusionTable.Index a (b + c) at s
  apply (Coeff.component_eq_self_iff (a + b + c)
    (i + FusionTable.indexParity b c r +
      FusionTable.indexParity a (b + c) s) (m r s)).2
  have hentry := hcolumn (realTRightPairSemanticEquiv a b c (r, s))
  rw [realTRightSemanticColumn_apply_semanticPair] at hentry
  have hpar := GaugeChi.gbrNativeIndexEquiv_parity ℝ realGauge a b c
    (FusionTable.frameIndex b c r, FusionTable.frameIndex a (b + c) s)
  rw [← realTRightPairSemanticEquiv_apply a b c r s] at hpar
  rw [← hpar] at hentry
  have hentry' :
      (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
          (realTSemanticCoeff (a + b + c) (m r s)) ∈
        (realGauge.D (a + (b + c))).grading
          (i + FusionTable.indexParity b c r +
            FusionTable.indexParity a (b + c) s) := by
    simpa only [realGauge_size,
      realTIndexParity_eq_sumParity, add_assoc] using hentry
  have hback := realGauge.gaugeCast_mem_grading
    (_root_.add_assoc a b c).symm hentry'
  rw [← realGauge.gaugeCast_symm_apply (_root_.add_assoc a b c),
    (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv.symm_apply_apply]
      at hback
  exact (realTSemanticCoeff_mem_iff_memGrade (a + b + c) _ _).1 hback

/-- The forward raw connector shifts route degree by its stored parity.  The
only connector input is the saved uniform semantic membership theorem. -/
theorem realT_hom_grade (a b c : ZMod 8) (i : ZMod 2)
    (m : realTData.LeftCarrier a b c)
    (hm : realTData.leftRoute.MemGrade a b c i m) :
    realTData.rightRoute.MemGrade a b c
      (i + realTData.parity a b c) (realTData.hom a b c m) := by
  apply realTRight_memGrade_of_semantic a b c
    (i + realTData.parity a b c) (realTHom a b c m)
  rw [realTHom_semantic]
  have hmem := RModCoordinate.RawSemanticSkeletalData.forward_mem a b c
  have hgraded :=
    (Bimod.mem_homGrading
      (GaugeChi.GBL.grading realGauge a b c)
      (GaugeChi.GBR.grading realGauge a b c)).mp
      ((GaugeChi.mem_gInterSpace_iff ℝ realGauge a b c).mp hmem).1
      i (realTLeftSemantic a b c m)
      (realTLeftSemantic_mem_grading a b c i m hm)
  simpa [RModCoordinate.RawSemanticSkeletalData.parity,
    realTData, realTParity] using hgraded

/-! ### Semantic realization of the three left-action slots

The saved semantic connector is already super-equivariant in each of the
three coefficient slots.  The next two lemmas merely transport a raw finite
matrix action to the corresponding semantic column; the six entry lemmas
then identify the raw route kernels with the existing semantic slot
matrices. -/

private theorem realTLeftSemanticColumn_matrixAction (a b c : ZMod 8)
    (K : FusionTable.Index a b → FusionTable.Index (a + b) c →
      FusionTable.Index a b → FusionTable.Index (a + b) c →
        Coeff (a + b + c))
    (M : Matrix
      (Fin (realGauge.gaugeSizeL a b c).1 ⊕
        Fin (realGauge.gaugeSizeL a b c).2)
      (Fin (realGauge.gaugeSizeL a b c).1 ⊕
        Fin (realGauge.gaugeSizeL a b c).2)
      (realGauge.D (a + b + c)).carrier)
    (hK : ∀ targetAB targetABC sourceAB sourceABC,
      realTSemanticCoeff (a + b + c)
          (K targetAB targetABC sourceAB sourceABC) =
        M (realTLeftPairSemanticEquiv a b c (targetAB, targetABC))
          (realTLeftPairSemanticEquiv a b c (sourceAB, sourceABC)))
    (m : FusionTable.Index a b → FusionTable.Index (a + b) c → Coeff (a + b + c)) :
    realTLeftSemanticColumn a b c (realTMatrixAction K m) =
      Matrix.mulVec M (realTLeftSemanticColumn a b c m) := by
  classical
  funext I
  obtain ⟨target, rfl⟩ := (realTLeftPairSemanticEquiv a b c).surjective I
  rcases target with ⟨targetAB, targetABC⟩
  rw [realTLeftSemanticColumn_apply_semanticPair]
  change realTSemanticCoeff (a + b + c)
      (realTMatrixAction K m targetAB targetABC) =
    ∑ J, M (realTLeftPairSemanticEquiv a b c (targetAB, targetABC)) J *
      realTLeftSemanticColumn a b c m J
  rw [realTMatrixAction_eq_pair_sum, realTSemanticCoeff_sum]
  conv_rhs =>
    rw [← Equiv.sum_comp (realTLeftPairSemanticEquiv a b c)
      (fun J =>
        M (realTLeftPairSemanticEquiv a b c (targetAB, targetABC)) J *
          realTLeftSemanticColumn a b c m J)]
  apply Finset.sum_congr rfl
  intro source _
  rcases source with ⟨sourceAB, sourceABC⟩
  rw [realTSemanticCoeff_mul, hK,
    realTLeftSemanticColumn_apply_semanticPair]

private theorem realTRightSemanticColumn_matrixAction (a b c : ZMod 8)
    (K : FusionTable.Index b c → FusionTable.Index a (b + c) →
      FusionTable.Index b c → FusionTable.Index a (b + c) →
        Coeff (a + b + c))
    (M : Matrix
      (Fin (realGauge.gaugeSizeR a b c).1 ⊕
        Fin (realGauge.gaugeSizeR a b c).2)
      (Fin (realGauge.gaugeSizeR a b c).1 ⊕
        Fin (realGauge.gaugeSizeR a b c).2)
      (realGauge.D (a + (b + c))).carrier)
    (hK : ∀ targetBC targetABC sourceBC sourceABC,
      (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
          (realTSemanticCoeff (a + b + c)
            (K targetBC targetABC sourceBC sourceABC)) =
        M (realTRightPairSemanticEquiv a b c (targetBC, targetABC))
          (realTRightPairSemanticEquiv a b c (sourceBC, sourceABC)))
    (m : FusionTable.Index b c → FusionTable.Index a (b + c) → Coeff (a + b + c)) :
    realTRightSemanticColumn a b c (realTMatrixAction K m) =
      Matrix.mulVec M (realTRightSemanticColumn a b c m) := by
  classical
  funext I
  obtain ⟨target, rfl⟩ := (realTRightPairSemanticEquiv a b c).surjective I
  rcases target with ⟨targetBC, targetABC⟩
  rw [realTRightSemanticColumn_apply_semanticPair]
  change (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
      (realTSemanticCoeff (a + b + c)
        (realTMatrixAction K m targetBC targetABC)) =
    ∑ J, M (realTRightPairSemanticEquiv a b c (targetBC, targetABC)) J *
      realTRightSemanticColumn a b c m J
  rw [realTMatrixAction_eq_pair_sum, realTSemanticCoeff_sum, map_sum]
  simp_rw [realTSemanticCoeff_mul, map_mul]
  conv_rhs =>
    rw [← Equiv.sum_comp (realTRightPairSemanticEquiv a b c)
      (fun J =>
        M (realTRightPairSemanticEquiv a b c (targetBC, targetABC)) J *
          realTRightSemanticColumn a b c m J)]
  apply Finset.sum_congr rfl
  intro source _
  rcases source with ⟨sourceBC, sourceABC⟩
  rw [hK, realTRightSemanticColumn_apply_semanticPair]

private theorem realTLeftASlotEntry_semantic (a b c : ZMod 8)
    (targetAB : FusionTable.Index a b)
    (targetABC : FusionTable.Index (a + b) c)
    (sourceAB : FusionTable.Index a b)
    (sourceABC : FusionTable.Index (a + b) c) (x : Coeff a) :
    realTSemanticCoeff (a + b + c)
        (leftRouteCoeff realCData a b c targetAB targetABC
          sourceAB sourceABC x (Coeff.one b) (Coeff.one c)) =
      (realGauge.gaugeRouteL a b c).toAlgEquiv
        (GaugeChi.aSlot ℝ realGauge a b c (realTSemanticCoeff a x))
        (realTLeftPairSemanticEquiv a b c (targetAB, targetABC))
        (realTLeftPairSemanticEquiv a b c (sourceAB, sourceABC)) := by
  change Coeff.semantic (a + b + c)
      (leftRouteCoeff realCData a b c targetAB targetABC
        sourceAB sourceABC x (Coeff.one b) (Coeff.one c)) =
    (realGauge.gaugeRouteL a b c).toAlgEquiv
      (GaugeChi.aSlot ℝ realGauge a b c (Coeff.semantic a x))
      (realTLeftPairSemanticEquiv a b c (targetAB, targetABC))
      (realTLeftPairSemanticEquiv a b c (sourceAB, sourceABC))
  rw [leftRouteCoeff_eq_fusionCoefficient, realRouteRowTwist_one,
    FusionTableLaws.semantic_fusionCoefficient_eq_semanticEntry,
    FusionTableLaws.semantic_fusionCoefficient_eq_semanticEntry,
    Coeff.semantic_one, Coeff.semantic_one,
    GaugeChi.routeL_aSlot_entry]
  simp only [realTLeftPairSemanticEquiv_symm_apply,
    FusionTableLaws.semanticFusionEntry_apply,
    FusionTableLaws.semanticFusionMatrix_apply,
    FusionTableLaws.semanticPureTensor_apply, realGauge_fuse]
  rfl

private theorem realTLeftBSlotEntry_semantic (a b c : ZMod 8)
    (targetAB : FusionTable.Index a b)
    (targetABC : FusionTable.Index (a + b) c)
    (sourceAB : FusionTable.Index a b)
    (sourceABC : FusionTable.Index (a + b) c) (y : Coeff b) :
    realTSemanticCoeff (a + b + c)
        (leftRouteCoeff realCData a b c targetAB targetABC
          sourceAB sourceABC (Coeff.one a) y (Coeff.one c)) =
      (realGauge.gaugeRouteL a b c).toAlgEquiv
        (GaugeChi.bSlot ℝ realGauge a b c (realTSemanticCoeff b y))
        (realTLeftPairSemanticEquiv a b c (targetAB, targetABC))
        (realTLeftPairSemanticEquiv a b c (sourceAB, sourceABC)) := by
  change Coeff.semantic (a + b + c)
      (leftRouteCoeff realCData a b c targetAB targetABC
        sourceAB sourceABC (Coeff.one a) y (Coeff.one c)) =
    (realGauge.gaugeRouteL a b c).toAlgEquiv
      (GaugeChi.bSlot ℝ realGauge a b c (Coeff.semantic b y))
      (realTLeftPairSemanticEquiv a b c (targetAB, targetABC))
      (realTLeftPairSemanticEquiv a b c (sourceAB, sourceABC))
  rw [leftRouteCoeff_eq_fusionCoefficient, realRouteRowTwist_one,
    FusionTableLaws.semantic_fusionCoefficient_eq_semanticEntry,
    FusionTableLaws.semantic_fusionCoefficient_eq_semanticEntry,
    Coeff.semantic_one, Coeff.semantic_one,
    GaugeChi.routeL_bSlot_entry]
  simp only [realTLeftPairSemanticEquiv_symm_apply,
    FusionTableLaws.semanticFusionEntry_apply,
    FusionTableLaws.semanticFusionMatrix_apply,
    FusionTableLaws.semanticPureTensor_apply, realGauge_fuse]
  rfl

private theorem realTLeftCSlotEntry_semantic (a b c : ZMod 8)
    (k : ZMod 2)
    (targetAB : FusionTable.Index a b)
    (targetABC : FusionTable.Index (a + b) c)
    (sourceAB : FusionTable.Index a b)
    (sourceABC : FusionTable.Index (a + b) c) (z : Coeff c)
    (hz : Coeff.MemGrade c k z) :
    realTSemanticCoeff (a + b + c)
        (leftRouteCoeff realCData a b c targetAB targetABC
          sourceAB sourceABC (Coeff.one a) (Coeff.one b) z) =
      (realGauge.gaugeRouteL a b c).toAlgEquiv
        (GaugeChi.cSlot ℝ realGauge a b c (realTSemanticCoeff c z))
        (realTLeftPairSemanticEquiv a b c (targetAB, targetABC))
        (realTLeftPairSemanticEquiv a b c (sourceAB, sourceABC)) := by
  change Coeff.semantic (a + b + c)
      (leftRouteCoeff realCData a b c targetAB targetABC
        sourceAB sourceABC (Coeff.one a) (Coeff.one b) z) =
    (realGauge.gaugeRouteL a b c).toAlgEquiv
      (GaugeChi.cSlot ℝ realGauge a b c (realTSemanticCoeff c z))
      (realTLeftPairSemanticEquiv a b c (targetAB, targetABC))
      (realTLeftPairSemanticEquiv a b c (sourceAB, sourceABC))
  have hzsem := realTSemanticCoeff_mem_of_memGrade c k z hz
  rw [leftRouteCoeff_eq_fusionCoefficient,
    realRouteRowTwist_of_memGrade c (indexParity a b sourceAB) k z hz,
    FusionTableLaws.fusionCoefficient_one,
    GaugeChi.routeL_cSlot_entry ℝ realGauge a b c hzsem]
  rw [realTLeftPairSemanticEquiv_symm_apply a b c targetAB targetABC,
    realTLeftPairSemanticEquiv_symm_apply a b c sourceAB sourceABC]
  simp only [realGauge_size]
  by_cases h : targetAB = sourceAB
  · subst sourceAB
    rw [if_pos rfl, if_pos rfl,
      FusionTableLaws.semantic_fusionCoefficient_eq_semanticEntry,
      Coeff.semantic_one, Coeff.semantic_smul, map_smul,
      ← Int.cast_smul_eq_zsmul ℝ,
      realTIntSgnCast_eq_paritySign,
      realTIndexParity_eq_sumParity]
    rfl
  · have hframe : FusionTable.frameIndex a b targetAB ≠
        FusionTable.frameIndex a b sourceAB := by
      intro hframe
      exact h ((finSumFinEquiv.symm).injective hframe)
    rw [if_neg h, if_neg hframe,
      FusionTableLaws.fusionCoefficient_zero_left,
      Coeff.semantic_zero]
    rfl

private theorem realTRightASlotEntry_semantic (a b c : ZMod 8)
    (i : ZMod 2)
    (targetBC : FusionTable.Index b c)
    (targetABC : FusionTable.Index a (b + c))
    (sourceBC : FusionTable.Index b c)
    (sourceABC : FusionTable.Index a (b + c)) (x : Coeff a)
    (hx : Coeff.MemGrade a i x) :
    (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
        (realTSemanticCoeff (a + b + c)
          (rightRouteCoeff realCData a b c targetBC targetABC
            sourceBC sourceABC x (Coeff.one b) (Coeff.one c))) =
      GaugeChi.routeRMat ℝ realGauge a b c
        (GaugeChi.aSlot ℝ realGauge a b c (realTSemanticCoeff a x))
        (realTRightPairSemanticEquiv a b c (targetBC, targetABC))
        (realTRightPairSemanticEquiv a b c (sourceBC, sourceABC)) := by
  have hxsem := realTSemanticCoeff_mem_of_memGrade a i x hx
  rw [rightRouteCoeff_eq_cast, realTCoeffSemantic_rightCast_cancel]
  unfold realRightRouteCoeffRaw
  change Coeff.semantic (a + (b + c))
      (fusionCoefficient a (b + c) targetABC sourceABC
        (routeRowTwist realDData a (indexParity b c targetBC) x)
        (fusionCoefficient b c targetBC sourceBC
          (Coeff.one b) (Coeff.one c))) =
    GaugeChi.routeRMat ℝ realGauge a b c
      (GaugeChi.aSlot ℝ realGauge a b c (realTSemanticCoeff a x))
      (realTRightPairSemanticEquiv a b c (targetBC, targetABC))
      (realTRightPairSemanticEquiv a b c (sourceBC, sourceABC))
  rw [realRouteRowTwist_of_memGrade a (indexParity b c targetBC) i x hx,
    FusionTableLaws.fusionCoefficient_one,
    GaugeChi.routeRNative_aSlot_entry ℝ realGauge a b c hxsem]
  rw [realTRightPairSemanticEquiv_symm_apply a b c targetBC targetABC,
    realTRightPairSemanticEquiv_symm_apply a b c sourceBC sourceABC]
  simp only [realGauge_size]
  by_cases h : targetBC = sourceBC
  · subst sourceBC
    rw [if_pos rfl, if_pos rfl,
      FusionTableLaws.semantic_fusionCoefficient_eq_semanticEntry,
      Coeff.semantic_smul, Coeff.semantic_one, map_smul,
      ← Int.cast_smul_eq_zsmul ℝ,
      realTIntSgnCast_eq_paritySign,
      realTIndexParity_eq_sumParity]
    rfl
  · have hframe : FusionTable.frameIndex b c targetBC ≠
        FusionTable.frameIndex b c sourceBC := by
      intro hframe
      exact h ((finSumFinEquiv.symm).injective hframe)
    rw [if_neg h, if_neg hframe,
      FusionTableLaws.fusionCoefficient_zero_right,
      Coeff.semantic_zero]
    rfl

private theorem realTRightBSlotEntry_semantic (a b c : ZMod 8)
    (targetBC : FusionTable.Index b c)
    (targetABC : FusionTable.Index a (b + c))
    (sourceBC : FusionTable.Index b c)
    (sourceABC : FusionTable.Index a (b + c)) (y : Coeff b) :
    (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
        (realTSemanticCoeff (a + b + c)
          (rightRouteCoeff realCData a b c targetBC targetABC
            sourceBC sourceABC (Coeff.one a) y (Coeff.one c))) =
      GaugeChi.routeRMat ℝ realGauge a b c
        (GaugeChi.bSlot ℝ realGauge a b c (realTSemanticCoeff b y))
        (realTRightPairSemanticEquiv a b c (targetBC, targetABC))
        (realTRightPairSemanticEquiv a b c (sourceBC, sourceABC)) := by
  rw [rightRouteCoeff_eq_cast, realTCoeffSemantic_rightCast_cancel]
  unfold realRightRouteCoeffRaw
  change Coeff.semantic (a + (b + c))
      (fusionCoefficient a (b + c) targetABC sourceABC
        (routeRowTwist realDData a (indexParity b c targetBC) (Coeff.one a))
        (fusionCoefficient b c targetBC sourceBC y (Coeff.one c))) =
    GaugeChi.routeRMat ℝ realGauge a b c
      (GaugeChi.bSlot ℝ realGauge a b c (Coeff.semantic b y))
      (realTRightPairSemanticEquiv a b c (targetBC, targetABC))
      (realTRightPairSemanticEquiv a b c (sourceBC, sourceABC))
  rw [realRouteRowTwist_one,
    FusionTableLaws.semantic_fusionCoefficient_eq_semanticEntry,
    FusionTableLaws.semantic_fusionCoefficient_eq_semanticEntry,
    Coeff.semantic_one, Coeff.semantic_one,
    GaugeChi.routeRNative_bSlot_entry]
  simp only [realTRightPairSemanticEquiv_symm_apply,
    FusionTableLaws.semanticFusionEntry_apply,
    FusionTableLaws.semanticFusionMatrix_apply,
    FusionTableLaws.semanticPureTensor_apply, realGauge_fuse]
  rfl

private theorem realTRightCSlotEntry_semantic (a b c : ZMod 8)
    (targetBC : FusionTable.Index b c)
    (targetABC : FusionTable.Index a (b + c))
    (sourceBC : FusionTable.Index b c)
    (sourceABC : FusionTable.Index a (b + c)) (z : Coeff c) :
    (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
        (realTSemanticCoeff (a + b + c)
          (rightRouteCoeff realCData a b c targetBC targetABC
            sourceBC sourceABC (Coeff.one a) (Coeff.one b) z)) =
      GaugeChi.routeRMat ℝ realGauge a b c
        (GaugeChi.cSlot ℝ realGauge a b c (realTSemanticCoeff c z))
        (realTRightPairSemanticEquiv a b c (targetBC, targetABC))
        (realTRightPairSemanticEquiv a b c (sourceBC, sourceABC)) := by
  rw [rightRouteCoeff_eq_cast, realTCoeffSemantic_rightCast_cancel]
  unfold realRightRouteCoeffRaw
  change Coeff.semantic (a + (b + c))
      (fusionCoefficient a (b + c) targetABC sourceABC
        (routeRowTwist realDData a (indexParity b c targetBC) (Coeff.one a))
        (fusionCoefficient b c targetBC sourceBC (Coeff.one b) z)) =
    GaugeChi.routeRMat ℝ realGauge a b c
      (GaugeChi.cSlot ℝ realGauge a b c (Coeff.semantic c z))
      (realTRightPairSemanticEquiv a b c (targetBC, targetABC))
      (realTRightPairSemanticEquiv a b c (sourceBC, sourceABC))
  rw [realRouteRowTwist_one,
    FusionTableLaws.semantic_fusionCoefficient_eq_semanticEntry,
    FusionTableLaws.semantic_fusionCoefficient_eq_semanticEntry,
    Coeff.semantic_one, Coeff.semantic_one,
    GaugeChi.routeRNative_cSlot_entry]
  simp only [realTRightPairSemanticEquiv_symm_apply,
    FusionTableLaws.semanticFusionEntry_apply,
    FusionTableLaws.semanticFusionMatrix_apply,
    FusionTableLaws.semanticPureTensor_apply, realGauge_fuse]
  rfl

/- The semantic coordinate identifications respect ordinary real scalars,
and the right identification is faithful. -/

private theorem realTLeftSemantic_smul (a b c : ZMod 8) (q : ℝ)
    (m : FusionTable.Index a b → FusionTable.Index (a + b) c → Coeff (a + b + c)) :
    realTLeftSemantic a b c (realLeftRouteSmul a b c q m) =
      q • realTLeftSemantic a b c m := by
  change realTLeftSemantic a b c
      (fun r s => Coeff.smul (a + b + c) q (m r s)) =
    q • realTLeftSemantic a b c m
  apply (GaugeChi.gblColumnEquiv ℝ realGauge a b c).injective
  rw [realTLeftSemantic_toColumn, map_smul,
    realTLeftSemantic_toColumn]
  funext I
  obtain ⟨p, rfl⟩ := (realTLeftPairSemanticEquiv a b c).surjective I
  rcases p with ⟨r, s⟩
  calc
    realTLeftSemanticColumn a b c
        (fun r s => Coeff.smul (a + b + c) q (m r s))
        (realTLeftPairSemanticEquiv a b c (r, s)) =
      realTSemanticCoeff (a + b + c)
        (Coeff.smul (a + b + c) q (m r s)) :=
      realTLeftSemanticColumn_apply_semanticPair a b c _ r s
    _ = q • realTSemanticCoeff (a + b + c) (m r s) :=
      realTSemanticCoeff_smul (a + b + c) q (m r s)
    _ = q • realTLeftSemanticColumn a b c m
        (realTLeftPairSemanticEquiv a b c (r, s)) :=
      congrArg (fun v : (realGauge.D (a + b + c)).carrier => q • v)
        (realTLeftSemanticColumn_apply_semanticPair a b c m r s).symm
    _ = (q • realTLeftSemanticColumn a b c m)
        (realTLeftPairSemanticEquiv a b c (r, s)) := by
      rfl

private theorem realTRightSemantic_smul (a b c : ZMod 8) (q : ℝ)
    (m : FusionTable.Index b c → FusionTable.Index a (b + c) → Coeff (a + b + c)) :
    realTRightSemantic a b c (realRightRouteSmul a b c q m) =
      q • realTRightSemantic a b c m := by
  change realTRightSemantic a b c
      (fun r s => Coeff.smul (a + b + c) q (m r s)) =
    q • realTRightSemantic a b c m
  apply (GaugeChi.gbrNativeColumnEquiv ℝ realGauge a b c).injective
  rw [realTRightSemantic_toColumn, map_smul,
    realTRightSemantic_toColumn]
  funext I
  obtain ⟨p, rfl⟩ := (realTRightPairSemanticEquiv a b c).surjective I
  rcases p with ⟨r, s⟩
  calc
    realTRightSemanticColumn a b c
        (fun r s => Coeff.smul (a + b + c) q (m r s))
        (realTRightPairSemanticEquiv a b c (r, s)) =
      (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
        (realTSemanticCoeff (a + b + c)
          (Coeff.smul (a + b + c) q (m r s))) :=
      realTRightSemanticColumn_apply_semanticPair a b c _ r s
    _ = (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
        (q • realTSemanticCoeff (a + b + c) (m r s)) :=
      congrArg
        (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
        (realTSemanticCoeff_smul (a + b + c) q (m r s))
    _ = q • (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
        (realTSemanticCoeff (a + b + c) (m r s)) := by
      rw [map_smul]
    _ = q • realTRightSemanticColumn a b c m
        (realTRightPairSemanticEquiv a b c (r, s)) :=
      congrArg
        (fun v : (realGauge.D (a + (b + c))).carrier => q • v)
        (realTRightSemanticColumn_apply_semanticPair a b c m r s).symm
    _ = (q • realTRightSemanticColumn a b c m)
        (realTRightPairSemanticEquiv a b c (r, s)) := by
      rfl

private theorem realTRightSemantic_injective (a b c : ZMod 8) :
    Function.Injective (realTRightSemantic a b c) := by
  intro m n hmn
  have hcolumn := congrArg
    (GaugeChi.gbrNativeColumnEquiv ℝ realGauge a b c) hmn
  rw [realTRightSemantic_toColumn, realTRightSemantic_toColumn] at hcolumn
  funext r s
  have hentry := congrFun hcolumn
    (realTRightPairSemanticEquiv a b c (r, s))
  rw [realTRightSemanticColumn_apply_semanticPair,
    realTRightSemanticColumn_apply_semanticPair] at hentry
  exact (Coeff.semantic (a + b + c)).injective
    ((realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv.injective hentry)

/- Each raw single-slot route action is exactly the corresponding semantic
coefficient action.  The `GBL`/`GBR` embedding lemmas identify the triple
tensor slot with the route's registered coefficient-module action. -/

private theorem realTLeftSemantic_aSlot (a b c : ZMod 8)
    (x : Coeff a) (m : FusionTable.Index a b → FusionTable.Index (a + b) c → Coeff (a + b + c)) :
    realTLeftSemantic a b c
        (realLeftRouteLeftPure a b c x (Coeff.one b) (Coeff.one c) m) =
      realTSemanticCoeff a x • realTLeftSemantic a b c m := by
  let xa : (realGauge.D a).carrier := realTSemanticCoeff a x
  let Y := GaugeChi.aSlot ℝ realGauge a b c xa
  have hY : Y • realTLeftSemantic a b c m =
      xa • realTLeftSemantic a b c m :=
    GaugeChi.GBL.aEmbed ℝ realGauge a b c _ xa rfl Y rfl _
  apply (GaugeChi.gblColumnEquiv ℝ realGauge a b c).injective
  rw [realTLeftSemantic_toColumn, ← hY,
    GaugeChi.gblColumnEquiv_gtensor_smul,
    realTLeftSemantic_toColumn]
  change realTLeftSemanticColumn a b c
      (realTMatrixAction
        (fun targetAB targetABC sourceAB sourceABC =>
          leftRouteCoeff realCData a b c targetAB targetABC
            sourceAB sourceABC x (Coeff.one b) (Coeff.one c)) m) =
    Matrix.mulVec
      (show Matrix
          (Fin (realGauge.gaugeSizeL a b c).1 ⊕
            Fin (realGauge.gaugeSizeL a b c).2)
          (Fin (realGauge.gaugeSizeL a b c).1 ⊕
            Fin (realGauge.gaugeSizeL a b c).2)
          (realGauge.D (a + b + c)).carrier from
        (realGauge.gaugeRouteL a b c).toAlgEquiv Y)
      (realTLeftSemanticColumn a b c m)
  exact realTLeftSemanticColumn_matrixAction a b c _ _
    (fun targetAB targetABC sourceAB sourceABC =>
      realTLeftASlotEntry_semantic a b c targetAB targetABC
        sourceAB sourceABC x) m

private theorem realTLeftSemantic_bSlot (a b c : ZMod 8)
    (y : Coeff b) (m : FusionTable.Index a b → FusionTable.Index (a + b) c → Coeff (a + b + c)) :
    realTLeftSemantic a b c
        (realLeftRouteLeftPure a b c (Coeff.one a) y (Coeff.one c) m) =
      realTSemanticCoeff b y • realTLeftSemantic a b c m := by
  let yb : (realGauge.D b).carrier := realTSemanticCoeff b y
  let Y := GaugeChi.bSlot ℝ realGauge a b c yb
  have hY : Y • realTLeftSemantic a b c m =
      yb • realTLeftSemantic a b c m :=
    GaugeChi.GBL.bEmbed ℝ realGauge a b c _ yb rfl Y rfl _
  apply (GaugeChi.gblColumnEquiv ℝ realGauge a b c).injective
  rw [realTLeftSemantic_toColumn, ← hY,
    GaugeChi.gblColumnEquiv_gtensor_smul,
    realTLeftSemantic_toColumn]
  change realTLeftSemanticColumn a b c
      (realTMatrixAction
        (fun targetAB targetABC sourceAB sourceABC =>
          leftRouteCoeff realCData a b c targetAB targetABC
            sourceAB sourceABC (Coeff.one a) y (Coeff.one c)) m) =
    Matrix.mulVec
      (show Matrix
          (Fin (realGauge.gaugeSizeL a b c).1 ⊕
            Fin (realGauge.gaugeSizeL a b c).2)
          (Fin (realGauge.gaugeSizeL a b c).1 ⊕
            Fin (realGauge.gaugeSizeL a b c).2)
          (realGauge.D (a + b + c)).carrier from
        (realGauge.gaugeRouteL a b c).toAlgEquiv Y)
      (realTLeftSemanticColumn a b c m)
  exact realTLeftSemanticColumn_matrixAction a b c _ _
    (fun targetAB targetABC sourceAB sourceABC =>
      realTLeftBSlotEntry_semantic a b c targetAB targetABC
        sourceAB sourceABC y) m

private theorem realTLeftSemantic_cSlot (a b c : ZMod 8) (k : ZMod 2)
    (z : Coeff c) (hz : Coeff.MemGrade c k z)
    (m : FusionTable.Index a b → FusionTable.Index (a + b) c → Coeff (a + b + c)) :
    realTLeftSemantic a b c
        (realLeftRouteLeftPure a b c (Coeff.one a) (Coeff.one b) z m) =
      realTSemanticCoeff c z • realTLeftSemantic a b c m := by
  let zc : (realGauge.D c).carrier := realTSemanticCoeff c z
  let Y := GaugeChi.cSlot ℝ realGauge a b c zc
  have hY : Y • realTLeftSemantic a b c m =
      zc • realTLeftSemantic a b c m :=
    GaugeChi.GBL.cEmbed ℝ realGauge a b c Y zc rfl _
  apply (GaugeChi.gblColumnEquiv ℝ realGauge a b c).injective
  rw [realTLeftSemantic_toColumn, ← hY,
    GaugeChi.gblColumnEquiv_gtensor_smul,
    realTLeftSemantic_toColumn]
  change realTLeftSemanticColumn a b c
      (realTMatrixAction
        (fun targetAB targetABC sourceAB sourceABC =>
          leftRouteCoeff realCData a b c targetAB targetABC
            sourceAB sourceABC (Coeff.one a) (Coeff.one b) z) m) =
    Matrix.mulVec
      (show Matrix
          (Fin (realGauge.gaugeSizeL a b c).1 ⊕
            Fin (realGauge.gaugeSizeL a b c).2)
          (Fin (realGauge.gaugeSizeL a b c).1 ⊕
            Fin (realGauge.gaugeSizeL a b c).2)
          (realGauge.D (a + b + c)).carrier from
        (realGauge.gaugeRouteL a b c).toAlgEquiv Y)
      (realTLeftSemanticColumn a b c m)
  exact realTLeftSemanticColumn_matrixAction a b c _ _
    (fun targetAB targetABC sourceAB sourceABC =>
      realTLeftCSlotEntry_semantic a b c k targetAB targetABC
        sourceAB sourceABC z hz) m

private theorem realTRightSemantic_aSlot (a b c : ZMod 8) (i : ZMod 2)
    (x : Coeff a) (hx : Coeff.MemGrade a i x)
    (m : FusionTable.Index b c → FusionTable.Index a (b + c) → Coeff (a + b + c)) :
    realTRightSemantic a b c
        (realRightRouteLeftPure a b c x (Coeff.one b) (Coeff.one c) m) =
      realTSemanticCoeff a x • realTRightSemantic a b c m := by
  let xa : (realGauge.D a).carrier := realTSemanticCoeff a x
  let Y := GaugeChi.aSlot ℝ realGauge a b c xa
  have hY : Y • realTRightSemantic a b c m =
      xa • realTRightSemantic a b c m :=
    GaugeChi.GBR.aEmbed_smul ℝ realGauge a b c _ xa rfl Y rfl _
  apply (GaugeChi.gbrNativeColumnEquiv ℝ realGauge a b c).injective
  rw [realTRightSemantic_toColumn, ← hY,
    GaugeChi.gbrNativeColumnEquiv_gtensor_smul,
    realTRightSemantic_toColumn]
  change realTRightSemanticColumn a b c
      (realTMatrixAction
        (fun targetBC targetABC sourceBC sourceABC =>
          rightRouteCoeff realCData a b c targetBC targetABC
            sourceBC sourceABC x (Coeff.one b) (Coeff.one c)) m) =
    Matrix.mulVec (GaugeChi.routeRMat ℝ realGauge a b c Y)
      (realTRightSemanticColumn a b c m)
  exact realTRightSemanticColumn_matrixAction a b c _ _
    (fun targetBC targetABC sourceBC sourceABC =>
      realTRightASlotEntry_semantic a b c i targetBC targetABC
        sourceBC sourceABC x hx) m

private theorem realTRightSemantic_bSlot (a b c : ZMod 8)
    (y : Coeff b) (m : FusionTable.Index b c → FusionTable.Index a (b + c) → Coeff (a + b + c)) :
    realTRightSemantic a b c
        (realRightRouteLeftPure a b c (Coeff.one a) y (Coeff.one c) m) =
      realTSemanticCoeff b y • realTRightSemantic a b c m := by
  let yb : (realGauge.D b).carrier := realTSemanticCoeff b y
  let Y := GaugeChi.bSlot ℝ realGauge a b c yb
  have hY : Y • realTRightSemantic a b c m =
      yb • realTRightSemantic a b c m :=
    GaugeChi.GBR.bEmbed_smul ℝ realGauge a b c _ yb rfl Y rfl _
  apply (GaugeChi.gbrNativeColumnEquiv ℝ realGauge a b c).injective
  rw [realTRightSemantic_toColumn, ← hY,
    GaugeChi.gbrNativeColumnEquiv_gtensor_smul,
    realTRightSemantic_toColumn]
  change realTRightSemanticColumn a b c
      (realTMatrixAction
        (fun targetBC targetABC sourceBC sourceABC =>
          rightRouteCoeff realCData a b c targetBC targetABC
            sourceBC sourceABC (Coeff.one a) y (Coeff.one c)) m) =
    Matrix.mulVec (GaugeChi.routeRMat ℝ realGauge a b c Y)
      (realTRightSemanticColumn a b c m)
  exact realTRightSemanticColumn_matrixAction a b c _ _
    (fun targetBC targetABC sourceBC sourceABC =>
      realTRightBSlotEntry_semantic a b c targetBC targetABC
        sourceBC sourceABC y) m

private theorem realTRightSemantic_cSlot (a b c : ZMod 8)
    (z : Coeff c) (m : FusionTable.Index b c → FusionTable.Index a (b + c) → Coeff (a + b + c)) :
    realTRightSemantic a b c
        (realRightRouteLeftPure a b c (Coeff.one a) (Coeff.one b) z m) =
      realTSemanticCoeff c z • realTRightSemantic a b c m := by
  let zc : (realGauge.D c).carrier := realTSemanticCoeff c z
  let Y := GaugeChi.cSlot ℝ realGauge a b c zc
  have hY : Y • realTRightSemantic a b c m =
      zc • realTRightSemantic a b c m :=
    GaugeChi.GBR.cEmbed_smul ℝ realGauge a b c Y zc rfl _
  apply (GaugeChi.gbrNativeColumnEquiv ℝ realGauge a b c).injective
  rw [realTRightSemantic_toColumn, ← hY,
    GaugeChi.gbrNativeColumnEquiv_gtensor_smul,
    realTRightSemantic_toColumn]
  change realTRightSemanticColumn a b c
      (realTMatrixAction
        (fun targetBC targetABC sourceBC sourceABC =>
          rightRouteCoeff realCData a b c targetBC targetABC
            sourceBC sourceABC (Coeff.one a) (Coeff.one b) z) m) =
    Matrix.mulVec (GaugeChi.routeRMat ℝ realGauge a b c Y)
      (realTRightSemanticColumn a b c m)
  exact realTRightSemanticColumn_matrixAction a b c _ _
    (fun targetBC targetABC sourceBC sourceABC =>
      realTRightCSlotEntry_semantic a b c targetBC targetABC
        sourceBC sourceABC z) m

/- The three single-slot connector laws are now direct applications of the
three saved `superEquivariant` conjuncts. -/

private theorem realT_hom_aSlot (a b c : ZMod 8) (i : ZMod 2)
    (x : Coeff a) (hx : Coeff.MemGrade a i x)
    (m : FusionTable.Index a b → FusionTable.Index (a + b) c → Coeff (a + b + c)) :
    realTHom a b c
        (realLeftRouteLeftPure a b c x (Coeff.one b) (Coeff.one c) m) =
      realRightRouteSmul a b c (paritySign (realTParity a b c * i))
        (realRightRouteLeftPure a b c x (Coeff.one b) (Coeff.one c)
          (realTHom a b c m)) := by
  apply realTRightSemantic_injective a b c
  rw [realTHom_semantic, realTLeftSemantic_aSlot,
    realTRightSemantic_smul,
    realTRightSemantic_aSlot a b c i x hx,
    realTHom_semantic]
  have hmem := RModCoordinate.RawSemanticSkeletalData.forward_mem a b c
  have hslot :=
    (Bimod.mem_superEquivariant (realGauge.D a).grading).mp
      ((GaugeChi.mem_gInterSpace_iff ℝ realGauge a b c).mp hmem).2.1
      (realTSemanticCoeff_mem_of_memGrade a i x hx)
      (realTLeftSemantic a b c m)
  rw [← Int.cast_smul_eq_zsmul ℝ,
    realTIntSgnCast_eq_paritySign] at hslot
  simpa [RModCoordinate.RawSemanticSkeletalData.parity,
    realTParity] using hslot

private theorem realT_hom_bSlot (a b c : ZMod 8) (j : ZMod 2)
    (y : Coeff b) (hy : Coeff.MemGrade b j y)
    (m : FusionTable.Index a b → FusionTable.Index (a + b) c → Coeff (a + b + c)) :
    realTHom a b c
        (realLeftRouteLeftPure a b c (Coeff.one a) y (Coeff.one c) m) =
      realRightRouteSmul a b c (paritySign (realTParity a b c * j))
        (realRightRouteLeftPure a b c (Coeff.one a) y (Coeff.one c)
          (realTHom a b c m)) := by
  apply realTRightSemantic_injective a b c
  rw [realTHom_semantic, realTLeftSemantic_bSlot,
    realTRightSemantic_smul, realTRightSemantic_bSlot,
    realTHom_semantic]
  have hmem := RModCoordinate.RawSemanticSkeletalData.forward_mem a b c
  have hslot :=
    (Bimod.mem_superEquivariant (realGauge.D b).grading).mp
      ((GaugeChi.mem_gInterSpace_iff ℝ realGauge a b c).mp hmem).2.2.1
      (realTSemanticCoeff_mem_of_memGrade b j y hy)
      (realTLeftSemantic a b c m)
  rw [← Int.cast_smul_eq_zsmul ℝ,
    realTIntSgnCast_eq_paritySign] at hslot
  simpa [RModCoordinate.RawSemanticSkeletalData.parity,
    realTParity] using hslot

private theorem realT_hom_cSlot (a b c : ZMod 8) (k : ZMod 2)
    (z : Coeff c) (hz : Coeff.MemGrade c k z)
    (m : FusionTable.Index a b → FusionTable.Index (a + b) c → Coeff (a + b + c)) :
    realTHom a b c
        (realLeftRouteLeftPure a b c (Coeff.one a) (Coeff.one b) z m) =
      realRightRouteSmul a b c (paritySign (realTParity a b c * k))
        (realRightRouteLeftPure a b c (Coeff.one a) (Coeff.one b) z
          (realTHom a b c m)) := by
  apply realTRightSemantic_injective a b c
  rw [realTHom_semantic, realTLeftSemantic_cSlot a b c k z hz,
    realTRightSemantic_smul, realTRightSemantic_cSlot,
    realTHom_semantic]
  have hmem := RModCoordinate.RawSemanticSkeletalData.forward_mem a b c
  have hslot :=
    (Bimod.mem_superEquivariant (realGauge.D c).grading).mp
      ((GaugeChi.mem_gInterSpace_iff ℝ realGauge a b c).mp hmem).2.2.2.1
      (realTSemanticCoeff_mem_of_memGrade c k z hz)
      (realTLeftSemantic a b c m)
  rw [← Int.cast_smul_eq_zsmul ℝ,
    realTIntSgnCast_eq_paritySign] at hslot
  simpa [RModCoordinate.RawSemanticSkeletalData.parity,
    realTParity] using hslot

/- Coordinate homogeneity is exactly the abstract algebra's fixed-point
condition for its stored executable projection. -/

private theorem realTCoeffMemGrade_toData (a : ZMod 8) (i : ZMod 2)
    (x : Coeff a) (hx : Coeff.MemGrade a i x) :
    (realDData.algebra a).MemGrade i x :=
  (Coeff.component_eq_self_iff a i x).2 hx

/- Ordered slot actions multiply without an additional Koszul sign.  This
is the order `a` outside `b` outside `c`; it is exactly the order needed to
assemble the three single-slot connector laws. -/

private theorem realTLeftPure_decompose (a b c : ZMod 8) (j : ZMod 2)
    (x : Coeff a) (y : Coeff b) (z : Coeff c)
    (hy : Coeff.MemGrade b j y) (m : FusionTable.Index a b → FusionTable.Index (a + b) c → Coeff (a + b + c)) :
    realLeftRouteLeftPure a b c x y z m =
      realLeftRouteLeftPure a b c x (Coeff.one b) (Coeff.one c)
        (realLeftRouteLeftPure a b c (Coeff.one a) y (Coeff.one c)
          (realLeftRouteLeftPure a b c (Coeff.one a) (Coeff.one b) z m)) := by
  have hxy (n : FusionTable.Index a b →
      FusionTable.Index (a + b) c → Coeff (a + b + c)) :
      realLeftRouteLeftPure a b c x (Coeff.one b) (Coeff.one c)
          (realLeftRouteLeftPure a b c (Coeff.one a) y (Coeff.one c) n) =
        realLeftRouteLeftPure a b c x y (Coeff.one c) n := by
    have h := realLeftRouteLaws.left_mul a b c 0 0 0 j
      x (Coeff.one a) (Coeff.one b) y (Coeff.one c) (Coeff.one c) n
      (realTCoeffMemGrade_toData b 0 _ (Coeff.memGrade_one b))
      (realTCoeffMemGrade_toData c 0 _ (Coeff.memGrade_one c))
      (realTCoeffMemGrade_toData a 0 _ (Coeff.memGrade_one a))
      (realTCoeffMemGrade_toData b j y hy)
    simp [paritySign] at h
    rw [realLeftRouteLaws.one_smul] at h
    simpa only [realLeftRouteData, realDData, coordinateSuperAlgebraData,
      Coeff.mul_one, Coeff.one_mul] using h
  have hxyz :
      realLeftRouteLeftPure a b c x y (Coeff.one c)
          (realLeftRouteLeftPure a b c (Coeff.one a) (Coeff.one b) z m) =
        realLeftRouteLeftPure a b c x y z m := by
    have h := realLeftRouteLaws.left_mul a b c 0 j 0 0
      x (Coeff.one a) y (Coeff.one b) (Coeff.one c) z m
      (realTCoeffMemGrade_toData b j y hy)
      (realTCoeffMemGrade_toData c 0 _ (Coeff.memGrade_one c))
      (realTCoeffMemGrade_toData a 0 _ (Coeff.memGrade_one a))
      (realTCoeffMemGrade_toData b 0 _ (Coeff.memGrade_one b))
    simp [paritySign] at h
    rw [realLeftRouteLaws.one_smul] at h
    simpa only [realLeftRouteData, realDData, coordinateSuperAlgebraData,
      Coeff.mul_one, Coeff.one_mul] using h
  rw [← hxyz, ← hxy]

private theorem realTRightPure_decompose (a b c : ZMod 8) (j : ZMod 2)
    (x : Coeff a) (y : Coeff b) (z : Coeff c)
    (hy : Coeff.MemGrade b j y) (m : FusionTable.Index b c → FusionTable.Index a (b + c) → Coeff (a + b + c)) :
    realRightRouteLeftPure a b c x y z m =
      realRightRouteLeftPure a b c x (Coeff.one b) (Coeff.one c)
        (realRightRouteLeftPure a b c (Coeff.one a) y (Coeff.one c)
          (realRightRouteLeftPure a b c (Coeff.one a) (Coeff.one b) z m)) := by
  have hxy (n : FusionTable.Index b c →
      FusionTable.Index a (b + c) → Coeff (a + b + c)) :
      realRightRouteLeftPure a b c x (Coeff.one b) (Coeff.one c)
          (realRightRouteLeftPure a b c (Coeff.one a) y (Coeff.one c) n) =
        realRightRouteLeftPure a b c x y (Coeff.one c) n := by
    have h := realRightRouteLaws.left_mul a b c 0 0 0 j
      x (Coeff.one a) (Coeff.one b) y (Coeff.one c) (Coeff.one c) n
      (realTCoeffMemGrade_toData b 0 _ (Coeff.memGrade_one b))
      (realTCoeffMemGrade_toData c 0 _ (Coeff.memGrade_one c))
      (realTCoeffMemGrade_toData a 0 _ (Coeff.memGrade_one a))
      (realTCoeffMemGrade_toData b j y hy)
    simp [paritySign] at h
    rw [realRightRouteLaws.one_smul] at h
    simpa only [realRightRouteData, realDData, coordinateSuperAlgebraData,
      Coeff.mul_one, Coeff.one_mul] using h
  have hxyz :
      realRightRouteLeftPure a b c x y (Coeff.one c)
          (realRightRouteLeftPure a b c (Coeff.one a) (Coeff.one b) z m) =
        realRightRouteLeftPure a b c x y z m := by
    have h := realRightRouteLaws.left_mul a b c 0 j 0 0
      x (Coeff.one a) y (Coeff.one b) (Coeff.one c) z m
      (realTCoeffMemGrade_toData b j y hy)
      (realTCoeffMemGrade_toData c 0 _ (Coeff.memGrade_one c))
      (realTCoeffMemGrade_toData a 0 _ (Coeff.memGrade_one a))
      (realTCoeffMemGrade_toData b 0 _ (Coeff.memGrade_one b))
    simp [paritySign] at h
    rw [realRightRouteLaws.one_smul] at h
    simpa only [realRightRouteData, realDData, coordinateSuperAlgebraData,
      Coeff.mul_one, Coeff.one_mul] using h
  rw [← hxyz, ← hxy]

/- The following two wrappers expose the abstract right-route module laws in
the exact executable spelling used by the public connector theorem. -/

private theorem realTRightLeftPure_smul_module (a b c : ZMod 8) (q : ℝ)
    (x : Coeff a) (y : Coeff b) (z : Coeff c)
    (m : RealRightRouteCarrier a b c) :
    realRightRouteLeftPure a b c x y z
        (realRightRouteSmul a b c q m) =
      realRightRouteSmul a b c q
        (realRightRouteLeftPure a b c x y z m) := by
  simpa only [realRightRouteData] using
    realRightRouteLaws.left_smul_module a b c q x y z m

private theorem realTRightRoute_smul_assoc (a b c : ZMod 8) (q r : ℝ)
    (m : RealRightRouteCarrier a b c) :
    realRightRouteSmul a b c (q * r) m =
      realRightRouteSmul a b c q (realRightRouteSmul a b c r m) := by
  simpa only [realRightRouteData] using
    realRightRouteLaws.smul_assoc a b c q r m

private theorem realTRightRoute_one_smul (a b c : ZMod 8)
    (m : RealRightRouteCarrier a b c) :
    realRightRouteSmul a b c 1 m = m := by
  simpa only [realRightRouteData] using
    realRightRouteLaws.one_smul a b c m

private theorem realTRightRoute_smul_sq_cancel (a b c : ZMod 8) (q : ℝ)
    (hq : q * q = 1) (m : realTData.RightCarrier a b c) :
    m = realTData.rightRoute.smul a b c q
      (realTData.rightRoute.smul a b c q m) := by
  let m' : RealRightRouteCarrier a b c := m
  change m' = realRightRouteSmul a b c q
    (realRightRouteSmul a b c q m')
  rw [← realTRightRoute_smul_assoc, hq, realTRightRoute_one_smul]

private theorem realTParitySign_three (p i j k : ZMod 2) :
    paritySign (p * i) * paritySign (p * j) * paritySign (p * k) =
      paritySign (p * (i + j + k)) := by
  rw [← realTParitySign_add, ← realTParitySign_add]
  congr 1
  ring

/-- The raw forward connector is super-equivariant for the full pure
three-slot action. -/
theorem realT_hom_left (a b c : ZMod 8) (i j k : ZMod 2)
    (x : Coeff a) (y : Coeff b) (z : Coeff c)
    (m : realTData.LeftCarrier a b c)
    (hx : Coeff.MemGrade a i x) (hy : Coeff.MemGrade b j y)
    (hz : Coeff.MemGrade c k z) :
    realTData.hom a b c
        (realTData.leftRoute.leftPure a b c x y z m) =
      realTData.rightRoute.smul a b c
        (paritySign (realTData.parity a b c * (i + j + k)))
        (realTData.rightRoute.leftPure a b c x y z
          (realTData.hom a b c m)) := by
  let m' : RealLeftRouteCarrier a b c := m
  change realTHom a b c (realLeftRouteLeftPure a b c x y z m') =
    realRightRouteSmul a b c
      (paritySign (realTParity a b c * (i + j + k)))
      (realRightRouteLeftPure a b c x y z (realTHom a b c m'))
  rw [realTLeftPure_decompose a b c j x y z hy,
    realT_hom_aSlot a b c i x hx,
    realT_hom_bSlot a b c j y hy,
    realT_hom_cSlot a b c k z hz]
  rw [realTRightLeftPure_smul_module a b c
      (paritySign (realTParity a b c * j))
      x (Coeff.one b) (Coeff.one c),
    realTRightLeftPure_smul_module a b c
      (paritySign (realTParity a b c * k))
      (Coeff.one a) y (Coeff.one c),
    realTRightLeftPure_smul_module a b c
      (paritySign (realTParity a b c * k))
      x (Coeff.one b) (Coeff.one c)]
  rw [← realTRightPure_decompose a b c j x y z hy,
    ← realTRightRoute_smul_assoc,
    ← realTRightRoute_smul_assoc,
    realTParitySign_three]

/-! ## Completion of the concrete connector laws

The forward homogeneity theorem determines how the connector commutes with
the two grading projections.  The inverse laws then transport every remaining
forward law to the explicit reverse map, without inspecting its table again. -/

/- A vector homogeneous in the complementary right-route degree has zero
projection to the selected degree.  This uses only the stored additive and
complement laws of the route. -/
private theorem realTRightComponent_zero_of_complementaryGrade
    (a b c : ZMod 8) (i : ZMod 2) (m : RealRightRouteCarrier a b c)
    (hm : realRightRouteData.MemGrade a b c (i + 1) m) :
    realRightRouteData.component a b c i m =
      realRightRouteData.zero a b c := by
  have hsplit := realRightRouteLaws.component_complement a b c i m
  rw [hm] at hsplit
  calc
    realRightRouteData.component a b c i m =
        realRightRouteData.add a b c
          (realRightRouteData.component a b c i m)
          (realRightRouteData.zero a b c) :=
      (realRightRouteLaws.add_zero a b c _).symm
    _ = realRightRouteData.add a b c
        (realRightRouteData.component a b c i m)
        (realRightRouteData.add a b c m
          (realRightRouteData.neg a b c m)) := by
      exact congrArg
        (realRightRouteData.add a b c
          (realRightRouteData.component a b c i m))
        (realRightRouteLaws.add_neg a b c m).symm
    _ = realRightRouteData.add a b c
        (realRightRouteData.add a b c
          (realRightRouteData.component a b c i m) m)
        (realRightRouteData.neg a b c m) :=
      (realRightRouteLaws.add_assoc a b c
        (realRightRouteData.component a b c i m) m
        (realRightRouteData.neg a b c m)).symm
    _ = realRightRouteData.add a b c m
        (realRightRouteData.neg a b c m) := by
      exact congrArg
        (fun w => realRightRouteData.add a b c w
          (realRightRouteData.neg a b c m)) hsplit
    _ = realRightRouteData.zero a b c :=
      realRightRouteLaws.add_neg a b c m

/-- The raw forward connector commutes with the stored route projections,
shifting their degree by its frozen parity. -/
theorem realT_hom_component (a b c : ZMod 8) (i : ZMod 2)
    (m : realTData.LeftCarrier a b c) :
    realTData.hom a b c (realTData.leftRoute.component a b c i m) =
      realTData.rightRoute.component a b c
        (i + realTData.parity a b c) (realTData.hom a b c m) := by
  let mi : RealLeftRouteCarrier a b c :=
    realLeftRouteData.component a b c i m
  let mc : RealLeftRouteCarrier a b c :=
    realLeftRouteData.component a b c (i + 1) m
  have hmi : realTData.leftRoute.MemGrade a b c i mi := by
    exact realLeftRouteLaws.component_idem a b c i m
  have hmc : realTData.leftRoute.MemGrade a b c (i + 1) mc := by
    exact realLeftRouteLaws.component_idem a b c (i + 1) m
  have hfmi : realTData.rightRoute.MemGrade a b c
      (i + realTData.parity a b c) (realTData.hom a b c mi) :=
    realT_hom_grade a b c i mi hmi
  have hfmc : realTData.rightRoute.MemGrade a b c
      ((i + realTData.parity a b c) + 1) (realTData.hom a b c mc) := by
    simpa [add_assoc, add_comm, add_left_comm] using
      realT_hom_grade a b c (i + 1) mc hmc
  have hfmcZero : realTData.rightRoute.component a b c
      (i + realTData.parity a b c) (realTData.hom a b c mc) =
        realTData.rightRoute.zero a b c :=
    realTRightComponent_zero_of_complementaryGrade a b c
      (i + realTData.parity a b c) (realTData.hom a b c mc) hfmc
  have hsplit : realTData.leftRoute.add a b c mi mc = m := by
    change realLeftRouteData.add a b c mi mc = m
    simpa only [mi, mc] using
      realLeftRouteLaws.component_complement a b c i m
  change realTData.hom a b c mi =
    realTData.rightRoute.component a b c
      (i + realTData.parity a b c) (realTData.hom a b c m)
  calc
    realTData.hom a b c mi =
        realTData.rightRoute.component a b c
          (i + realTData.parity a b c) (realTData.hom a b c mi) :=
      hfmi.symm
    _ = realTData.rightRoute.add a b c
        (realTData.rightRoute.component a b c
          (i + realTData.parity a b c) (realTData.hom a b c mi))
        (realTData.rightRoute.zero a b c) :=
      (realRightRouteLaws.add_zero a b c _).symm
    _ = realTData.rightRoute.add a b c
        (realTData.rightRoute.component a b c
          (i + realTData.parity a b c) (realTData.hom a b c mi))
        (realTData.rightRoute.component a b c
          (i + realTData.parity a b c) (realTData.hom a b c mc)) := by
      rw [hfmcZero]
    _ = realTData.rightRoute.component a b c
        (i + realTData.parity a b c)
        (realTData.rightRoute.add a b c
          (realTData.hom a b c mi) (realTData.hom a b c mc)) :=
      (realRightRouteLaws.component_add a b c
        (i + realTData.parity a b c) _ _).symm
    _ = realTData.rightRoute.component a b c
        (i + realTData.parity a b c)
        (realTData.hom a b c (realTData.leftRoute.add a b c mi mc)) := by
      rw [realT_hom_add]
    _ = realTData.rightRoute.component a b c
        (i + realTData.parity a b c) (realTData.hom a b c m) := by
      rw [hsplit]

/- The explicit reverse map makes the forward map injective. -/
private theorem realT_hom_injective (a b c : ZMod 8) :
    Function.Injective (realTData.hom a b c) := by
  intro m n hmn
  have h := congrArg (realTData.inv a b c) hmn
  simpa only [realT_inv_hom_id] using h

/- Every parity sign is its own inverse. -/
private theorem realTParitySign_sq (i : ZMod 2) :
    paritySign i * paritySign i = 1 := by
  rcases zmod2_cases i with hi | hi <;> subst i <;>
    norm_num [paritySign]

/-- Super-equivariance of the explicit reverse connector follows by applying
the injective forward connector and cancelling the square of the sign. -/
theorem realT_inv_left (a b c : ZMod 8) (i j k : ZMod 2)
    (x : Coeff a) (y : Coeff b) (z : Coeff c)
    (m : realTData.RightCarrier a b c)
    (hx : Coeff.MemGrade a i x) (hy : Coeff.MemGrade b j y)
    (hz : Coeff.MemGrade c k z) :
    realTData.inv a b c
        (realTData.rightRoute.leftPure a b c x y z m) =
      realTData.leftRoute.smul a b c
        (paritySign (realTData.parity a b c * (i + j + k)))
        (realTData.leftRoute.leftPure a b c x y z
          (realTData.inv a b c m)) := by
  apply realT_hom_injective a b c
  rw [realT_hom_inv_id, realT_hom_smul,
    realT_hom_left a b c i j k x y z (realTData.inv a b c m) hx hy hz,
    realT_hom_inv_id]
  exact realTRightRoute_smul_sq_cancel a b c
    (paritySign (realTData.parity a b c * (i + j + k)))
    (realTParitySign_sq _) _

/-- The reverse connector commutes with route projections with the same
degree shift, since the connector parity has order two. -/
theorem realT_inv_component (a b c : ZMod 8) (i : ZMod 2)
    (m : realTData.RightCarrier a b c) :
    realTData.inv a b c (realTData.rightRoute.component a b c i m) =
      realTData.leftRoute.component a b c
        (i + realTData.parity a b c) (realTData.inv a b c m) := by
  apply realT_hom_injective a b c
  rw [realT_hom_inv_id, realT_hom_component, realT_hom_inv_id,
    add_assoc, Coeff.add_self_eq_zero, add_zero]

/-- The explicit reverse connector shifts homogeneous degree by the stored
connector parity. -/
theorem realT_inv_grade (a b c : ZMod 8) (i : ZMod 2)
    (m : realTData.RightCarrier a b c)
    (hm : realTData.rightRoute.MemGrade a b c i m) :
    realTData.leftRoute.MemGrade a b c
      (i + realTData.parity a b c) (realTData.inv a b c m) := by
  change realTData.leftRoute.component a b c
      (i + realTData.parity a b c) (realTData.inv a b c m) =
    realTData.inv a b c m
  rw [← realT_inv_component, hm]

/-- All laws of the exact executable real connector data. -/
theorem realTLaws : TLaws realDData realDLaws realCData realCLaws realTData where
  left_route_laws := realLeftRouteLaws
  right_route_laws := realRightRouteLaws
  left_ofCoord_toCoord := by intros; rfl
  left_toCoord_ofCoord := by intros; rfl
  right_ofCoord_toCoord := by intros; rfl
  right_toCoord_ofCoord := by intros; rfl
  left_toCoord_zero := by intros; rfl
  left_toCoord_add := by intros; rfl
  left_toCoord_neg := by intros; rfl
  left_toCoord_smul := by intros; rfl
  left_toCoord_component := by intros; rfl
  left_toCoord_leftPure := by intros; rfl
  left_toCoord_right := by intros; rfl
  right_toCoord_zero := by intros; rfl
  right_toCoord_add := by intros; rfl
  right_toCoord_neg := by intros; rfl
  right_toCoord_smul := by intros; rfl
  right_toCoord_component := by intros; rfl
  right_toCoord_leftPure := by intros; rfl
  right_toCoord_right := by intros; rfl
  hom_zero := realT_hom_zero
  hom_add := realT_hom_add
  hom_neg := realT_hom_neg
  hom_smul := realT_hom_smul
  inv_zero := realT_inv_zero
  inv_add := realT_inv_add
  inv_neg := realT_inv_neg
  inv_smul := realT_inv_smul
  hom_right := realT_hom_right
  inv_right := realT_inv_right
  hom_left := by
    intro a b c i j k x y z m hx hy hz
    exact realT_hom_left a b c i j k x y z m
      ((Coeff.component_eq_self_iff a i x).1 hx)
      ((Coeff.component_eq_self_iff b j y).1 hy)
      ((Coeff.component_eq_self_iff c k z).1 hz)
  inv_left := by
    intro a b c i j k x y z m hx hy hz
    exact realT_inv_left a b c i j k x y z m
      ((Coeff.component_eq_self_iff a i x).1 hx)
      ((Coeff.component_eq_self_iff b j y).1 hy)
      ((Coeff.component_eq_self_iff c k z).1 hz)
  hom_component := realT_hom_component
  inv_component := realT_inv_component
  hom_grade := realT_hom_grade
  inv_grade := realT_inv_grade
  hom_inv_id := realT_hom_inv_id
  inv_hom_id := realT_inv_hom_id

/-- The completed computable raw real connector. -/
def realT : T realD realC where
  data := realTData
  laws := realTLaws

/-! ## Closed reductions of the completed concrete connector -/

/-- The stored raw connector degree is exactly the frozen, unshifted parity
table (up to the additive/multiplicative label wrapper). -/
theorem realT_parity_eq_realLeanParityTable (a b c : ZMod 8) :
    realTData.parity a b c =
      GaugeChi.realLeanParityTable
        (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
          (Multiplicative.ofAdd c) :=
  rfl

/-- A nonzero connector degree, stated through the completed instance. -/
theorem realT_example_parity : realT.data.parity 1 1 4 = 1 := rfl

example : realT.data.parity 1 1 4 = 1 := realT_example_parity

/-- The completed instance exposes the certified inverse on a genuinely
rectangular route triple. -/
theorem realT_example_inv_hom
    (m : realT.data.LeftCarrier 1 4 4) :
    realT.data.inv 1 4 4 (realT.data.hom 1 4 4 m) = m :=
  realT.laws.inv_hom_id 1 4 4 m

example (m : realT.data.LeftCarrier 1 4 4) :
    realT.data.inv 1 4 4 (realT.data.hom 1 4 4 m) = m :=
  realT_example_inv_hom m

end Superfusion.RMod.RawDCT
