/-
Superfusion / GaugeChi / TripleCerts / FuseShadows

**GENERATED FILE — do not edit.**  Regenerate with

    python3 scripts/certgen/gen_triple_certs.py --shadows \
        --module FuseShadows \
        --out Superfusion/GaugeChi/TripleCerts/FuseShadows.lean

THE SHARED SHADOW MODULE.  Every per-triple certificate batch under
`GaugeChi/TripleCerts/` needs the integer shadow `fuseZ_a_b` of the frozen
`realFuseMatrix a b` literal at each of its (at most four) fusion corners,
together with the proof `hfuseZ_a_b : IsFuseZ a b fuseZ_a_b` that the shadow
is the literal.  A corner is shared by many triples, so before this module
each batch re-emitted the 12–21 shadows it happened to need and re-ran the
`fin_cases` grid that proves them.  All 64 corners are emitted here exactly
once, at the `TripleCerts` namespace, so the batches resolve the short names
`fuseZ_a_b` / `hfuseZ_a_b` unqualified and pay nothing for them.

Also hoisted, for the same reason: the three cast lemmas `castZ0`/`castZ1`/
`castZm1` the entrywise proof closes its goals with, the packed-literal
decoder `fuseCodeZ` / `fuseDecode_eq_intCast`, and the certificate consumer
`coeffOf_sumPos` / `realCheckMatEq_sumPos`.

WHAT IS PROVED HERE.  Nothing new: each `hfuseZ_a_b` is proved by rewriting
with the frozen `realFuseMatrix_a_b` theorem it was read from, so a drift
between this generated table and `Superfusion/Gauge/RealFuseSpec*.lean` is a
compile error rather than a silent disagreement.  `realCheckMatEq_sumPos`
instantiates `CoeffChecker.checkMatEq_sound_submatrix` and proves nothing
about the checker itself.

Every landed `realFuseMatrix` literal has entries in `{0, 1, -1}`, and at a
literal index both the `!![…]` literal and `matGet` whnf to one of the three,
so each entry of each `IsFuseZ` is a DEFEQ check against one of the three
cast lemmas.  (`norm_num` per entry is ~8x slower: 100 s versus 12 s on the
`32 × 32` branch `(2,3)`.)

Corners: 64 (37 bang, 15 one, 12 packed), 9649 entrywise goals.

No `sorry`, no `native_decide`, no new axioms.
-/
import Superfusion.GaugeChi.RouteBridgeProto
import Superfusion.Gauge.RealFuseSpecPeel
import Superfusion.Gauge.RealFuseSpecPeel2
import Superfusion.Gauge.RealFuseSpecPeel3
import Superfusion.Gauge.RealFuseSpecPilot
import Superfusion.Gauge.RealFuseSpecQuat
import Superfusion.Gauge.RealFuseSpecQuat2
import Superfusion.Gauge.RealFuseSpecQuat3
import Superfusion.Gauge.RealFuseSpecTower
import Superfusion.Gauge.RealFuseSpecTransposeClose
import Superfusion.Gauge.RealFuseSpecWrap
import Superfusion.Gauge.RealFuseSpecWrap2
import Superfusion.Gauge.RealFuseSpecWrap3
import Superfusion.Gauge.RealFuseSpecWrap4

namespace Superfusion
namespace GaugeChi
namespace TripleCerts

open Module

/-! ### The packed-literal decoder -/

/-- The integer shadow of `fuseDecode`: `0 ↦ 0`, `1 ↦ 1`, `2 ↦ -1`. -/
def fuseCodeZ : ℕ → ℤ
  | 1 => 1
  | 2 => -1
  | _ => 0

theorem fuseDecode_eq_intCast (n : ℕ) : fuseDecode n = ((fuseCodeZ n : ℤ) : ℝ) := by
  match n with
  | 0 => norm_num [fuseDecode, fuseCodeZ]
  | 1 => norm_num [fuseDecode, fuseCodeZ]
  | 2 => norm_num [fuseDecode, fuseCodeZ]
  | (_ + 3) =>
    show (0 : ℝ) = ((0 : ℤ) : ℝ)
    norm_num

/-! ### The certificate consumer, at the composite frame

`CoeffChecker.checkMatEq_sound_submatrix` already carries a checked integer
certificate along an arbitrary reindexing `ι ≃ Fin σ`.  The only thing
needed here is to name the reindexing of the composite frame
`Fin p ⊕ Fin q ≃ Fin (p + q)` and to observe that it agrees with `sumPos`,
the plain position function the certificate literals are written against.

NOTHING is proved about the checker here: `checkMatEq_sound_submatrix` is
applied, not re-derived, and the equivalence is discharged ONCE, outside
every per-entry and per-quadruple check. -/

theorem coeffOf_sumPos {p q k : ℕ} (Z : List (List (List ℤ))) :
    (fun (r s : Fin p ⊕ Fin q) =>
        coeffOf (p + q) k Z (finSumFinEquiv r) (finSumFinEquiv s))
      = fun r s (g : Fin k) => coeffGet Z (sumPos r) (sumPos s) g.val := by
  funext r s g
  rcases r with i | i <;> rcases s with j | j <;> rfl

/-- **The consumer**: a `true` integer certificate on pre-transported list
literals gives the matrix identity `X · T = c • (T · Y)` over `D_m` in the
composite frame `Fin p ⊕ Fin q`. -/
theorem realCheckMatEq_sumPos (m : ZMod 8) (p q : ℕ) (c : ℤ)
    (X T Y : List (List (List ℤ)))
    (hchk : checkMatEq (p + q) (realRepDim m.val) (realCoN m.val)
      (realSignN m.val) c X T Y = true) :
    matOfCoeff (ι := Fin p ⊕ Fin q) (realRepBasis m)
          (fun r s g => coeffGet X (sumPos r) (sumPos s) g.val)
        * matOfCoeff (realRepBasis m)
          (fun r s g => coeffGet T (sumPos r) (sumPos s) g.val)
      = c • (matOfCoeff (realRepBasis m)
            (fun r s g => coeffGet T (sumPos r) (sumPos s) g.val)
          * matOfCoeff (realRepBasis m)
            (fun r s g => coeffGet Y (sumPos r) (sumPos s) g.val)) := by
  have key := checkMatEq_sound_submatrix (finSumFinEquiv (m := p) (n := q))
    (realRepBasisAux m.val) (realRepBasisAux_mul m.val)
    (realRepMulIdxAux_involutive m.val) (realRepMulIdxAux_involutive m.val)
    c X T Y hchk
  simp only [coeffOf_sumPos] at key
  exact key

theorem castZ0 : ((0 : ℤ) : ℝ) = 0 := Int.cast_zero

theorem castZ1 : ((1 : ℤ) : ℝ) = 1 := Int.cast_one

theorem castZm1 : ((-1 : ℤ) : ℝ) = -1 := by norm_num

/-! ### Integer shadows of the fusion matrices, all 64 corners -/

/-- Integer shadow of the frozen `realFuseMatrix 0 0` literal. -/
def fuseZ_0_0 : Fin 1 → Fin 1 → ℤ := fun f col => matGet
  [[1]]
  f.val col.val

theorem hfuseZ_0_0 : IsFuseZ 0 0 fuseZ_0_0 := by
  intro f col
  rw [realFuseMatrix_zero_left_0]
  fin_cases f; fin_cases col; exact castZ1.symm

/-- Integer shadow of the frozen `realFuseMatrix 0 1` literal. -/
def fuseZ_0_1 : Fin 2 → Fin 2 → ℤ := fun f col => matGet
  [[1, 0],
    [0, 1]]
  f.val col.val

theorem hfuseZ_0_1 : IsFuseZ 0 1 fuseZ_0_1 := by
  intro f col
  rw [realFuseMatrix_zero_left_1]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm

/-- Integer shadow of the frozen `realFuseMatrix 0 2` literal. -/
def fuseZ_0_2 : Fin 4 → Fin 4 → ℤ := fun f col => matGet
  [[1, 0, 0, 0],
    [0, 1, 0, 0],
    [0, 0, 1, 0],
    [0, 0, 0, 1]]
  f.val col.val

theorem hfuseZ_0_2 : IsFuseZ 0 2 fuseZ_0_2 := by
  intro f col
  rw [realFuseMatrix_zero_left_2]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm

/-- Integer shadow of the frozen `realFuseMatrix 0 3` literal. -/
def fuseZ_0_3 : Fin 8 → Fin 8 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 1]]
  f.val col.val

theorem hfuseZ_0_3 : IsFuseZ 0 3 fuseZ_0_3 := by
  intro f col
  rw [realFuseMatrix_zero_left_3]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm

/-- Integer shadow of the frozen `realFuseMatrix 0 4` literal. -/
def fuseZ_0_4 : Fin 4 → Fin 4 → ℤ := fun f col => matGet
  [[1, 0, 0, 0],
    [0, 1, 0, 0],
    [0, 0, 1, 0],
    [0, 0, 0, 1]]
  f.val col.val

theorem hfuseZ_0_4 : IsFuseZ 0 4 fuseZ_0_4 := by
  intro f col
  rw [realFuseMatrix_zero_left_4]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm

/-- Integer shadow of the frozen `realFuseMatrix 0 5` literal. -/
def fuseZ_0_5 : Fin 8 → Fin 8 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 1]]
  f.val col.val

theorem hfuseZ_0_5 : IsFuseZ 0 5 fuseZ_0_5 := by
  intro f col
  rw [realFuseMatrix_zero_left_5]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm

/-- Integer shadow of the frozen `realFuseMatrix 0 6` literal. -/
def fuseZ_0_6 : Fin 4 → Fin 4 → ℤ := fun f col => matGet
  [[1, 0, 0, 0],
    [0, 1, 0, 0],
    [0, 0, 1, 0],
    [0, 0, 0, 1]]
  f.val col.val

theorem hfuseZ_0_6 : IsFuseZ 0 6 fuseZ_0_6 := by
  intro f col
  rw [realFuseMatrix_zero_left_6]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm

/-- Integer shadow of the frozen `realFuseMatrix 0 7` literal. -/
def fuseZ_0_7 : Fin 2 → Fin 2 → ℤ := fun f col => matGet
  [[1, 0],
    [0, 1]]
  f.val col.val

theorem hfuseZ_0_7 : IsFuseZ 0 7 fuseZ_0_7 := by
  intro f col
  rw [realFuseMatrix_zero_left_7]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm

/-- Integer shadow of the frozen `realFuseMatrix 1 0` literal. -/
def fuseZ_1_0 : Fin 2 → Fin 2 → ℤ := fun f col => matGet
  [[1, 0],
    [0, 1]]
  f.val col.val

theorem hfuseZ_1_0 : IsFuseZ 1 0 fuseZ_1_0 := by
  intro f col
  rw [realFuseMatrix_zero_right_1]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm

/-- Integer shadow of the frozen `realFuseMatrix 1 1` literal. -/
def fuseZ_1_1 : Fin 4 → Fin 4 → ℤ := fun f col => matGet
  [[1, 0, 0, 0],
    [0, 0, 1, 0],
    [0, 1, 0, 0],
    [0, 0, 0, 1]]
  f.val col.val

theorem hfuseZ_1_1 : IsFuseZ 1 1 fuseZ_1_1 := by
  intro f col
  rw [realFuseMatrix_one_one]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm

/-- Integer shadow of the frozen `realFuseMatrix 1 2` literal. -/
def fuseZ_1_2 : Fin 8 → Fin 8 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1]]
  f.val col.val

theorem hfuseZ_1_2 : IsFuseZ 1 2 fuseZ_1_2 := by
  intro f col
  rw [realFuseMatrix_1_2]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm

/-- Integer shadow of the frozen `realFuseMatrix 1 3` literal. -/
def fuseZ_1_3 : Fin 16 → Fin 16 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0],
    [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0],
    [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
    [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]
  f.val col.val

set_option maxHeartbeats 800000 in
theorem hfuseZ_1_3 : IsFuseZ 1 3 fuseZ_1_3 := by
  intro f col
  rw [realFuseMatrix_1_3]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 1 4` literal. -/
def fuseZ_1_4 : Fin 8 → Fin 8 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, -1, 0],
    [0, 0, 0, 0, 0, 0, 0, 1],
    [0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0]]
  f.val col.val

theorem hfuseZ_1_4 : IsFuseZ 1 4 fuseZ_1_4 := by
  intro f col
  rw [realFuseMatrix_1_4]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 1 5` literal. -/
def fuseZ_1_5 : Fin 16 → Fin 16 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
    [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]
  f.val col.val

set_option maxHeartbeats 800000 in
theorem hfuseZ_1_5 : IsFuseZ 1 5 fuseZ_1_5 := by
  intro f col
  rw [realFuseMatrix_1_5]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 1 6` literal. -/
def fuseZ_1_6 : Fin 8 → Fin 8 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 1, 0],
    [0, 1, 0, 0, 0, 0, 0, -1],
    [0, 0, 1, 0, 1, 0, 0, 0],
    [0, 0, 0, 1, 0, -1, 0, 0],
    [0, 0, 1, 0, -1, 0, 0, 0],
    [0, 0, 0, -1, 0, -1, 0, 0],
    [1, 0, 0, 0, 0, 0, -1, 0],
    [0, -1, 0, 0, 0, 0, 0, -1]]
  f.val col.val

theorem hfuseZ_1_6 : IsFuseZ 1 6 fuseZ_1_6 := by
  intro f col
  rw [realFuseMatrix_1_6]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 1 7` literal. -/
def fuseZ_1_7 : Fin 4 → Fin 4 → ℤ := fun f col => matGet
  [[1, 0, 0, 1],
    [0, 1, 1, 0],
    [0, 1, -1, 0],
    [1, 0, 0, -1]]
  f.val col.val

theorem hfuseZ_1_7 : IsFuseZ 1 7 fuseZ_1_7 := by
  intro f col
  rw [realFuseMatrix_1_7]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 2 0` literal. -/
def fuseZ_2_0 : Fin 4 → Fin 4 → ℤ := fun f col => matGet
  [[1, 0, 0, 0],
    [0, 1, 0, 0],
    [0, 0, 1, 0],
    [0, 0, 0, 1]]
  f.val col.val

theorem hfuseZ_2_0 : IsFuseZ 2 0 fuseZ_2_0 := by
  intro f col
  rw [realFuseMatrix_zero_right_2]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm

/-- Integer shadow of the frozen `realFuseMatrix 2 1` literal. -/
def fuseZ_2_1 : Fin 8 → Fin 8 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0],
    [0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1]]
  f.val col.val

theorem hfuseZ_2_1 : IsFuseZ 2 1 fuseZ_2_1 := by
  intro f col
  rw [realFuseMatrix_2_1]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm

/-- Integer shadow of the frozen `realFuseMatrix 2 2` literal. -/
def fuseZ_2_2 : Fin 16 → Fin 16 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]
  f.val col.val

set_option maxHeartbeats 800000 in
theorem hfuseZ_2_2 : IsFuseZ 2 2 fuseZ_2_2 := by
  intro f col
  rw [realFuseMatrix_2_2]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 2 3` literal. -/
def fuseZ_2_3 : Fin 32 → Fin 32 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]
  f.val col.val

set_option maxHeartbeats 3200000 in
theorem hfuseZ_2_3 : IsFuseZ 2 3 fuseZ_2_3 := by
  intro f col
  rw [realFuseMatrix_2_3]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 2 4` literal. -/
def fuseZ_2_4 : Fin 16 → Fin 16 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
    [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]]
  f.val col.val

set_option maxHeartbeats 800000 in
theorem hfuseZ_2_4 : IsFuseZ 2 4 fuseZ_2_4 := by
  intro f col
  rw [realFuseMatrix_2_4]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 2 5` literal. -/
def fuseZ_2_5 : Fin 32 → Fin 32 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
    [0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0],
    [0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0],
    [0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
    [0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]
  f.val col.val

set_option maxHeartbeats 3200000 in
theorem hfuseZ_2_5 : IsFuseZ 2 5 fuseZ_2_5 := by
  intro f col
  rw [realFuseMatrix_2_5]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 2 6` literal. -/
def fuseZ_2_6 : Fin 16 → Fin 16 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1],
    [0, 0, 0, 1, 0, 0, 1, 0, 0, -1, 0, 0, 1, 0, 0, 0],
    [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0],
    [0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, -1, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0, 0],
    [1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1],
    [0, 0, 1, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, -1, 0, 0],
    [0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0],
    [0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0],
    [0, 0, 1, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 1, 0, 0],
    [1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
    [0, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 1, 0, 0],
    [0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0],
    [0, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0, 1, 0, 0, 0],
    [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1]]
  f.val col.val

set_option maxHeartbeats 800000 in
theorem hfuseZ_2_6 : IsFuseZ 2 6 fuseZ_2_6 := by
  intro f col
  rw [realFuseMatrix_2_6]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 2 7` literal. -/
def fuseZ_2_7 : Fin 8 → Fin 8 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 1],
    [0, 1, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 1, 0],
    [0, 1, 0, 0, -1, 0, 0, 0],
    [0, 0, 0, -1, 0, 0, 1, 0],
    [1, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, -1, 0, 0, 0, 0, 1]]
  f.val col.val

theorem hfuseZ_2_7 : IsFuseZ 2 7 fuseZ_2_7 := by
  intro f col
  rw [realFuseMatrix_2_7]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 3 0` literal. -/
def fuseZ_3_0 : Fin 8 → Fin 8 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 1]]
  f.val col.val

theorem hfuseZ_3_0 : IsFuseZ 3 0 fuseZ_3_0 := by
  intro f col
  rw [realFuseMatrix_zero_right_3]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm

/-- Integer shadow of the frozen `realFuseMatrix 3 1` literal. -/
def fuseZ_3_1 : Fin 16 → Fin 16 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
    [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]]
  f.val col.val

set_option maxHeartbeats 800000 in
theorem hfuseZ_3_1 : IsFuseZ 3 1 fuseZ_3_1 := by
  intro f col
  rw [realFuseMatrix_3_1]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 3 2` literal. -/
def fuseZ_3_2 : Fin 32 → Fin 32 → ℤ :=
  fun f col => fuseCodeZ (fuseRows_3_2 f / 3 ^ (col : ℕ) % 3)

theorem hfuseZ_3_2 : IsFuseZ 3 2 fuseZ_3_2 := by
  intro f col
  rw [realFuseMatrix_3_2 f col]
  exact fuseDecode_eq_intCast _

/-- Integer shadow of the frozen `realFuseMatrix 3 3` literal. -/
def fuseZ_3_3 : Fin 64 → Fin 64 → ℤ :=
  fun f col => fuseCodeZ (fuseRows_3_3 f / 3 ^ (col : ℕ) % 3)

theorem hfuseZ_3_3 : IsFuseZ 3 3 fuseZ_3_3 := by
  intro f col
  rw [realFuseMatrix_3_3 f col]
  exact fuseDecode_eq_intCast _

/-- Integer shadow of the frozen `realFuseMatrix 3 4` literal. -/
def fuseZ_3_4 : Fin 32 → Fin 32 → ℤ :=
  fun f col => fuseCodeZ (fuseRows_3_4 f / 3 ^ (col : ℕ) % 3)

theorem hfuseZ_3_4 : IsFuseZ 3 4 fuseZ_3_4 := by
  intro f col
  rw [realFuseMatrix_3_4 f col]
  exact fuseDecode_eq_intCast _

/-- Integer shadow of the frozen `realFuseMatrix 3 5` literal. -/
def fuseZ_3_5 : Fin 64 → Fin 64 → ℤ :=
  fun f col => fuseCodeZ (fuseRows_3_5 f / 3 ^ (col : ℕ) % 3)

theorem hfuseZ_3_5 : IsFuseZ 3 5 fuseZ_3_5 := by
  intro f col
  rw [realFuseMatrix_3_5 f col]
  exact fuseDecode_eq_intCast _

/-- Integer shadow of the frozen `realFuseMatrix 3 6` literal. -/
def fuseZ_3_6 : Fin 32 → Fin 32 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
    [1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
    [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0],
    [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
    [1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
    [0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0],
    [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1]]
  f.val col.val

set_option maxHeartbeats 3200000 in
theorem hfuseZ_3_6 : IsFuseZ 3 6 fuseZ_3_6 := by
  intro f col
  rw [realFuseMatrix_3_6]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 3 7` literal. -/
def fuseZ_3_7 : Fin 16 → Fin 16 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    [0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0],
    [1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
    [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1]]
  f.val col.val

set_option maxHeartbeats 800000 in
theorem hfuseZ_3_7 : IsFuseZ 3 7 fuseZ_3_7 := by
  intro f col
  rw [realFuseMatrix_3_7]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 4 0` literal. -/
def fuseZ_4_0 : Fin 4 → Fin 4 → ℤ := fun f col => matGet
  [[1, 0, 0, 0],
    [0, 1, 0, 0],
    [0, 0, 1, 0],
    [0, 0, 0, 1]]
  f.val col.val

theorem hfuseZ_4_0 : IsFuseZ 4 0 fuseZ_4_0 := by
  intro f col
  rw [realFuseMatrix_zero_right_4]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm

/-- Integer shadow of the frozen `realFuseMatrix 4 1` literal. -/
def fuseZ_4_1 : Fin 8 → Fin 8 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, -1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 1, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0]]
  f.val col.val

theorem hfuseZ_4_1 : IsFuseZ 4 1 fuseZ_4_1 := by
  intro f col
  rw [realFuseMatrix_4_1]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 4 2` literal. -/
def fuseZ_4_2 : Fin 16 → Fin 16 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0],
    [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
    [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1],
    [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0],
    [0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
  f.val col.val

set_option maxHeartbeats 800000 in
theorem hfuseZ_4_2 : IsFuseZ 4 2 fuseZ_4_2 := by
  intro f col
  rw [realFuseMatrix_4_2]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 4 3` literal. -/
def fuseZ_4_3 : Fin 32 → Fin 32 → ℤ :=
  fun f col => fuseCodeZ (fuseRows_4_3 f / 3 ^ (col : ℕ) % 3)

theorem hfuseZ_4_3 : IsFuseZ 4 3 fuseZ_4_3 := by
  intro f col
  rw [realFuseMatrix_4_3 f col]
  exact fuseDecode_eq_intCast _

/-- Integer shadow of the frozen `realFuseMatrix 4 4` literal. -/
def fuseZ_4_4 : Fin 16 → Fin 16 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
    [0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0],
    [0, 0, 1, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, 1, 0, 0, -1, 0, 0, 1, 0, 0, -1, 0, 0, 0],
    [0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0],
    [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1],
    [0, 0, 0, -1, 0, 0, 1, 0, 0, 1, 0, 0, -1, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, -1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0],
    [1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1],
    [0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0],
    [0, 0, 0, -1, 0, 0, -1, 0, 0, 1, 0, 0, 1, 0, 0, 0],
    [0, 0, -1, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 1, 0, 0],
    [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0],
    [1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1]]
  f.val col.val

set_option maxHeartbeats 800000 in
theorem hfuseZ_4_4 : IsFuseZ 4 4 fuseZ_4_4 := by
  intro f col
  rw [realFuseMatrix_4_4]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 4 5` literal. -/
def fuseZ_4_5 : Fin 32 → Fin 32 → ℤ :=
  fun f col => fuseCodeZ (fuseRows_4_5 f / 3 ^ (col : ℕ) % 3)

theorem hfuseZ_4_5 : IsFuseZ 4 5 fuseZ_4_5 := by
  intro f col
  rw [realFuseMatrix_4_5 f col]
  exact fuseDecode_eq_intCast _

/-- Integer shadow of the frozen `realFuseMatrix 4 6` literal. -/
def fuseZ_4_6 : Fin 16 → Fin 16 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0],
    [0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1],
    [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
    [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0],
    [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
  f.val col.val

set_option maxHeartbeats 800000 in
theorem hfuseZ_4_6 : IsFuseZ 4 6 fuseZ_4_6 := by
  intro f col
  rw [realFuseMatrix_4_6]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 4 7` literal. -/
def fuseZ_4_7 : Fin 8 → Fin 8 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, -1],
    [0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, -1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, -1, 0],
    [0, 0, 0, 0, 1, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0]]
  f.val col.val

theorem hfuseZ_4_7 : IsFuseZ 4 7 fuseZ_4_7 := by
  intro f col
  rw [realFuseMatrix_4_7]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 5 0` literal. -/
def fuseZ_5_0 : Fin 8 → Fin 8 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 1]]
  f.val col.val

theorem hfuseZ_5_0 : IsFuseZ 5 0 fuseZ_5_0 := by
  intro f col
  rw [realFuseMatrix_zero_right_5]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm

/-- Integer shadow of the frozen `realFuseMatrix 5 1` literal. -/
def fuseZ_5_1 : Fin 16 → Fin 16 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    [0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0],
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
    [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]]
  f.val col.val

set_option maxHeartbeats 800000 in
theorem hfuseZ_5_1 : IsFuseZ 5 1 fuseZ_5_1 := by
  intro f col
  rw [realFuseMatrix_5_1]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 5 2` literal. -/
def fuseZ_5_2 : Fin 32 → Fin 32 → ℤ :=
  fun f col => fuseCodeZ (fuseRows_5_2 f / 3 ^ (col : ℕ) % 3)

theorem hfuseZ_5_2 : IsFuseZ 5 2 fuseZ_5_2 := by
  intro f col
  rw [realFuseMatrix_5_2 f col]
  exact fuseDecode_eq_intCast _

/-- Integer shadow of the frozen `realFuseMatrix 5 3` literal. -/
def fuseZ_5_3 : Fin 64 → Fin 64 → ℤ :=
  fun f col => fuseCodeZ (fuseRows_5_3 f / 3 ^ (col : ℕ) % 3)

theorem hfuseZ_5_3 : IsFuseZ 5 3 fuseZ_5_3 := by
  intro f col
  rw [realFuseMatrix_5_3 f col]
  exact fuseDecode_eq_intCast _

/-- Integer shadow of the frozen `realFuseMatrix 5 4` literal. -/
def fuseZ_5_4 : Fin 32 → Fin 32 → ℤ :=
  fun f col => fuseCodeZ (fuseRows_5_4 f / 3 ^ (col : ℕ) % 3)

theorem hfuseZ_5_4 : IsFuseZ 5 4 fuseZ_5_4 := by
  intro f col
  rw [realFuseMatrix_5_4 f col]
  exact fuseDecode_eq_intCast _

/-- Integer shadow of the frozen `realFuseMatrix 5 5` literal. -/
def fuseZ_5_5 : Fin 64 → Fin 64 → ℤ :=
  fun f col => fuseCodeZ (fuseRows_5_5 f / 3 ^ (col : ℕ) % 3)

theorem hfuseZ_5_5 : IsFuseZ 5 5 fuseZ_5_5 := by
  intro f col
  rw [realFuseMatrix_5_5 f col]
  exact fuseDecode_eq_intCast _

/-- Integer shadow of the frozen `realFuseMatrix 5 6` literal. -/
def fuseZ_5_6 : Fin 32 → Fin 32 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]
  f.val col.val

set_option maxHeartbeats 3200000 in
theorem hfuseZ_5_6 : IsFuseZ 5 6 fuseZ_5_6 := by
  intro f col
  rw [realFuseMatrix_5_6]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 5 7` literal. -/
def fuseZ_5_7 : Fin 16 → Fin 16 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    [0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
    [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0],
    [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0]]
  f.val col.val

set_option maxHeartbeats 800000 in
theorem hfuseZ_5_7 : IsFuseZ 5 7 fuseZ_5_7 := by
  intro f col
  rw [realFuseMatrix_5_7]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 6 0` literal. -/
def fuseZ_6_0 : Fin 4 → Fin 4 → ℤ := fun f col => matGet
  [[1, 0, 0, 0],
    [0, 1, 0, 0],
    [0, 0, 1, 0],
    [0, 0, 0, 1]]
  f.val col.val

theorem hfuseZ_6_0 : IsFuseZ 6 0 fuseZ_6_0 := by
  intro f col
  rw [realFuseMatrix_zero_right_6]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm

/-- Integer shadow of the frozen `realFuseMatrix 6 1` literal. -/
def fuseZ_6_1 : Fin 8 → Fin 8 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, -1],
    [0, 1, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 1, 0],
    [0, -1, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, -1, 0],
    [1, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, -1, 0, 0, 0, 0, -1]]
  f.val col.val

theorem hfuseZ_6_1 : IsFuseZ 6 1 fuseZ_6_1 := by
  intro f col
  rw [realFuseMatrix_6_1]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 6 2` literal. -/
def fuseZ_6_2 : Fin 16 → Fin 16 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1],
    [0, 0, 0, 1, 0, 0, 1, 0, 0, -1, 0, 0, 1, 0, 0, 0],
    [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0],
    [0, 0, 1, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, -1, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0, 0],
    [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1],
    [0, 0, -1, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, -1, 0, 0],
    [0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0],
    [0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0],
    [0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1, 0, 0],
    [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1],
    [0, 0, 0, -1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0],
    [0, 0, -1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0],
    [0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0],
    [0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, -1, 0, 0, 0],
    [1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]]
  f.val col.val

set_option maxHeartbeats 800000 in
theorem hfuseZ_6_2 : IsFuseZ 6 2 fuseZ_6_2 := by
  intro f col
  rw [realFuseMatrix_6_2]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 6 3` literal. -/
def fuseZ_6_3 : Fin 32 → Fin 32 → ℤ :=
  fun f col => fuseCodeZ (fuseRows_6_3 f / 3 ^ (col : ℕ) % 3)

theorem hfuseZ_6_3 : IsFuseZ 6 3 fuseZ_6_3 := by
  intro f col
  rw [realFuseMatrix_6_3 f col]
  exact fuseDecode_eq_intCast _

/-- Integer shadow of the frozen `realFuseMatrix 6 4` literal. -/
def fuseZ_6_4 : Fin 16 → Fin 16 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0]]
  f.val col.val

set_option maxHeartbeats 800000 in
theorem hfuseZ_6_4 : IsFuseZ 6 4 fuseZ_6_4 := by
  intro f col
  rw [realFuseMatrix_6_4]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 6 5` literal. -/
def fuseZ_6_5 : Fin 32 → Fin 32 → ℤ :=
  fun f col => fuseCodeZ (fuseRows_6_5 f / 3 ^ (col : ℕ) % 3)

theorem hfuseZ_6_5 : IsFuseZ 6 5 fuseZ_6_5 := by
  intro f col
  rw [realFuseMatrix_6_5 f col]
  exact fuseDecode_eq_intCast _

/-- Integer shadow of the frozen `realFuseMatrix 6 6` literal. -/
def fuseZ_6_6 : Fin 16 → Fin 16 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
    [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0],
    [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0]]
  f.val col.val

set_option maxHeartbeats 800000 in
theorem hfuseZ_6_6 : IsFuseZ 6 6 fuseZ_6_6 := by
  intro f col
  rw [realFuseMatrix_6_6]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 6 7` literal. -/
def fuseZ_6_7 : Fin 8 → Fin 8 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0],
    [0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1]]
  f.val col.val

theorem hfuseZ_6_7 : IsFuseZ 6 7 fuseZ_6_7 := by
  intro f col
  rw [realFuseMatrix_6_7]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm

/-- Integer shadow of the frozen `realFuseMatrix 7 0` literal. -/
def fuseZ_7_0 : Fin 2 → Fin 2 → ℤ := fun f col => matGet
  [[1, 0],
    [0, 1]]
  f.val col.val

theorem hfuseZ_7_0 : IsFuseZ 7 0 fuseZ_7_0 := by
  intro f col
  rw [realFuseMatrix_zero_right_7]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm

/-- Integer shadow of the frozen `realFuseMatrix 7 1` literal. -/
def fuseZ_7_1 : Fin 4 → Fin 4 → ℤ := fun f col => matGet
  [[1, 0, 0, -1],
    [0, 1, 1, 0],
    [0, -1, 1, 0],
    [1, 0, 0, 1]]
  f.val col.val

theorem hfuseZ_7_1 : IsFuseZ 7 1 fuseZ_7_1 := by
  intro f col
  rw [realFuseMatrix_7_1]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 7 2` literal. -/
def fuseZ_7_2 : Fin 8 → Fin 8 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, -1, 0],
    [0, 1, 0, 0, 0, 0, 0, 1],
    [0, 0, 1, 0, 1, 0, 0, 0],
    [0, 0, 0, 1, 0, -1, 0, 0],
    [0, 0, -1, 0, 1, 0, 0, 0],
    [0, 0, 0, 1, 0, 1, 0, 0],
    [1, 0, 0, 0, 0, 0, 1, 0],
    [0, -1, 0, 0, 0, 0, 0, 1]]
  f.val col.val

theorem hfuseZ_7_2 : IsFuseZ 7 2 fuseZ_7_2 := by
  intro f col
  rw [realFuseMatrix_7_2]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 7 3` literal. -/
def fuseZ_7_3 : Fin 16 → Fin 16 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    [0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]
  f.val col.val

set_option maxHeartbeats 800000 in
theorem hfuseZ_7_3 : IsFuseZ 7 3 fuseZ_7_3 := by
  intro f col
  rw [realFuseMatrix_7_3]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 7 4` literal. -/
def fuseZ_7_4 : Fin 8 → Fin 8 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, -1, 0],
    [0, 0, 0, 0, 0, 0, 0, -1],
    [0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, -1, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0]]
  f.val col.val

theorem hfuseZ_7_4 : IsFuseZ 7 4 fuseZ_7_4 := by
  intro f col
  rw [realFuseMatrix_7_4]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 7 5` literal. -/
def fuseZ_7_5 : Fin 16 → Fin 16 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0]]
  f.val col.val

set_option maxHeartbeats 800000 in
theorem hfuseZ_7_5 : IsFuseZ 7 5 fuseZ_7_5 := by
  intro f col
  rw [realFuseMatrix_7_5]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm | exact castZm1.symm

/-- Integer shadow of the frozen `realFuseMatrix 7 6` literal. -/
def fuseZ_7_6 : Fin 8 → Fin 8 → ℤ := fun f col => matGet
  [[1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1]]
  f.val col.val

theorem hfuseZ_7_6 : IsFuseZ 7 6 fuseZ_7_6 := by
  intro f col
  rw [realFuseMatrix_7_6]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm

/-- Integer shadow of the frozen `realFuseMatrix 7 7` literal. -/
def fuseZ_7_7 : Fin 4 → Fin 4 → ℤ := fun f col => matGet
  [[1, 0, 0, 0],
    [0, 0, 1, 0],
    [0, 1, 0, 0],
    [0, 0, 0, 1]]
  f.val col.val

theorem hfuseZ_7_7 : IsFuseZ 7 7 fuseZ_7_7 := by
  intro f col
  rw [realFuseMatrix_7_7]
  fin_cases f <;> fin_cases col <;> first | exact castZ0.symm | exact castZ1.symm

end TripleCerts
end GaugeChi
end Superfusion
