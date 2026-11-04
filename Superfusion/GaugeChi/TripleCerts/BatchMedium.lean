/-
Superfusion / GaugeChi / TripleCerts / BatchMedium

**GENERATED FILE — do not edit.**  Regenerate with

    python3 scripts/certgen/gen_triple_certs.py \
        --triples 1,1,5 1,1,6 1,2,3 1,2,4 1,3,6 1,4,2 1,5,4 1,5,5 \
        --module BatchMedium \
        --out Superfusion/GaugeChi/TripleCerts/BatchMedium.lean

Uniform layer: `GaugeChi/RouteBridgeProto.lean` §§1–5 (the six
`route*_*Slot_coeff` bridge lemmas, `matOfCoeff_*`, `IsFuseZ`, `matGet`,
`sumPos`); arithmetic layer: `GaugeChi/CoeffChecker.lean`; assembly:
`gtOfT_mem_interSpace_of_realRepBasis` (`GaugeChi/RouteMatrixProto.lean`).
This file only instantiates them, triple by triple.

FRAME.  Every connector below is **pre-transported**: it is the `T_lean`
of `Data/certificates/real_lean_frame_transport.json`,
`T_lean r s = T_certgen (permR r) (permL s)`, and the nonvanishing
witness is the **transported** pivot of the same record.  `permL` and
`permR` appear nowhere in this file, and no frame transport of any kind
is evaluated by any check here.

WHAT EACH CHECK SEES.  Both routes are pre-tabulated too, so the work
splits into exactly two kinds of check, and the expensive one is pure data:

* the TABULATION `hXtab…`/`hYtab…` — `σ² · k` entries per route, the only
  place where the route's own frame equivalences (`ro`/`ri`, `lo`/`li`,
  `fuseRow`/`fuseCol`) are reduced, once per entry;
* the CONVOLUTION `checkMatEq` — `σ² · k` tests of `2 · σ · k` multiply-adds,
  reduced by `decide +kernel` on nested `List ℤ` LITERALS.  No `Equiv`, no
  `Fin` bound, no `Finset.sum` and no route formula occurs inside it.

Before the tabulation the convolution re-evaluated the route formula once
per multiply-add — `σ³ k²` times instead of `σ² k`.  At the heaviest triples
(`σ = k = 8`) that is a factor of 32, and it is why those certificates
could not be elaborated at all: `decide` exceeded `maxRecDepth`.

SOUNDNESS.  `checkMatEq` is consumed only through the existing
`CoeffChecker.checkMatEq_sound_submatrix`; `realCheckMatEq_sumPos` below
instantiates it and proves nothing about the checker itself.

Only `generic` (`hsz`) triples appear here — the 12 exceptional
`(a,4,4)`/`(4,4,c)` are carried on their own track, and the split is not
visible downstream of `Ttab`.

Triples (8): (1,1,5), (1,1,6), (1,2,3), (1,2,4), (1,3,6), (1,4,2), (1,5,4), (1,5,5).
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
import Superfusion.Gauge.RealFuseSpecWrap2
import Superfusion.Gauge.RealFuseSpecWrap3
import Superfusion.Gauge.RealFuseSpecWrap4

namespace Superfusion
namespace GaugeChi
namespace TripleCerts
namespace BatchMedium

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

/-! ### Integer shadows of the fusion matrices (hoisted, deduplicated)

Every landed `realFuseMatrix` literal has entries in `{0, 1, -1}`, and at
a literal index both the `!![…]` literal and `matGet` whnf to one of the
three, so each entry of each `IsFuseZ` is a DEFEQ check against one of
the three cast lemmas below.  (`norm_num` per entry is ~8x slower: 100 s
versus 12 s on the `32 × 32` branch `(2,3)`.) -/

/-! ### The certificate consumer, at the composite frame

`CoeffChecker.checkMatEq_sound_submatrix` already carries a checked integer
certificate along an arbitrary reindexing `ι ≃ Fin σ`.  The only thing
needed here is to name the reindexing of the composite frame
`Fin p ⊕ Fin q ≃ Fin (p + q)` and to observe that it agrees with `sumPos`,
the plain position function the literals below are written against.

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

/-- Integer shadow of the frozen `realFuseMatrix 5 2` literal. -/
def fuseZ_5_2 : Fin 32 → Fin 32 → ℤ :=
  fun f col => fuseCodeZ (fuseRows_5_2 f / 3 ^ (col : ℕ) % 3)

theorem hfuseZ_5_2 : IsFuseZ 5 2 fuseZ_5_2 := by
  intro f col
  rw [realFuseMatrix_5_2 f col]
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

/-! ### The triple `(1,1,5)`

`gaugeSizeL = gaugeSizeR = (2,2)`, `dim D_7 = 2`, certgen parity `0`; the unit-slot shortcut: the connector is the identity, so every certificate carries the sign `+1`. -/
section Triple_1_1_5
open Module
theorem hsz1_1_5 : realGauge.gaugeSizeR 1 1 5 = realGauge.gaugeSizeL 1 1 5 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`4 x 4 x 2`). -/
def TL1_1_5 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

/-- The same literal read at the composite frame `Fin 2 ⊕ Fin 2`. -/
noncomputable def Tc1_1_5 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet TL1_1_5 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_7`. -/
noncomputable def T1_1_5 : ((realGauge.D ((1 : ZMod 8) + 1 + 5)).matrixSuper
    (realGauge.gaugeSizeL 1 1 5).1 (realGauge.gaugeSizeL 1 1 5).2).carrier :=
  matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Tc1_1_5

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT1_1_5 : T1_1_5 ∈ ((realGauge.D ((1 : ZMod 8) + 1 + 5)).matrixSuper
    (realGauge.gaugeSizeL 1 1 5).1 (realGauge.gaugeSizeL 1 1 5).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((1 : ZMod 8) + 1 + 5) Tc1_1_5 0 (by decide)

theorem T1_1_5_ne_zero : T1_1_5 ≠ 0 :=
  matOfCoeff_ne_zero ((1 : ZMod 8) + 1 + 5) Tc1_1_5 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa1_1_5_0 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 I) = (ro (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (5 : ZMod 8)).1 (realSize (1 : ZMod 8) (5 : ZMod 8)).2 (ro (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 I)
          * realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((1 : ZMod 8) + 5) (ri (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 I) (ri (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 J) g) (fuseCol (1 : ZMod 8) ((1 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya1_1_5_0 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_1 (fuseRow (1 : ZMod 8) (1 : ZMod 8) (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_2_5 (fuseRow ((1 : ZMod 8) + 1) (5 : ZMod 8) (li (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 1) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa1_1_5_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa1_1_5_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xca1_1_5_0 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa1_1_5_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_1_5_0 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa1_1_5_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_1_5_0 : ∀ I J g, Xa1_1_5_0 I J g = Xca1_1_5_0 I J g := by
  decide +kernel

theorem hYtaba1_1_5_0 : ∀ I J g, Ya1_1_5_0 I J g = Yca1_1_5_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta1_1_5_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_1_5
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_1_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Xa1_1_5_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Xca1_1_5_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2)) (realRepBasis ((1 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_1_5_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Ya1_1_5_0 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_1_1 hfuseZ_2_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Yca1_1_5_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2)) (realRepBasis ((1 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_1_5_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 1 1 5).1 (realGauge.gaugeSizeL 1 1 5).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa1_1_5_0 TL1_1_5 YLa1_1_5_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa1_1_5_1 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 I) = (ro (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (5 : ZMod 8)).1 (realSize (1 : ZMod 8) (5 : ZMod 8)).2 (ro (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 I)
          * realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((1 : ZMod 8) + 5) (ri (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 I) (ri (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 J) g) (fuseCol (1 : ZMod 8) ((1 : ZMod 8) + 5) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya1_1_5_1 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_1 (fuseRow (1 : ZMod 8) (1 : ZMod 8) (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_2_5 (fuseRow ((1 : ZMod 8) + 1) (5 : ZMod 8) (li (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 1) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa1_1_5_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa1_1_5_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0]]]

noncomputable def Xca1_1_5_1 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa1_1_5_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_1_5_1 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa1_1_5_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_1_5_1 : ∀ I J g, Xa1_1_5_1 I J g = Xca1_1_5_1 I J g := by
  decide +kernel

theorem hYtaba1_1_5_1 : ∀ I J g, Ya1_1_5_1 I J g = Yca1_1_5_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta1_1_5_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_1_5
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_1_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Xa1_1_5_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 hfuseZ_1_6 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Xca1_1_5_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2)) (realRepBasis ((1 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_1_5_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Ya1_1_5_1 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_1_1 hfuseZ_2_5 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Yca1_1_5_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2)) (realRepBasis ((1 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_1_5_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 1 1 5).1 (realGauge.gaugeSizeL 1 1 5).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa1_1_5_1 TL1_1_5 YLa1_1_5_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb1_1_5_0 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 I) (ro (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((1 : ZMod 8) + 5) (ri (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 I) (ri (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 J) g) (fuseCol (1 : ZMod 8) ((1 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb1_1_5_0 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_1 (fuseRow (1 : ZMod 8) (1 : ZMod 8) (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_2_5 (fuseRow ((1 : ZMod 8) + 1) (5 : ZMod 8) (li (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 1) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb1_1_5_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb1_1_5_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcb1_1_5_0 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb1_1_5_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_1_5_0 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb1_1_5_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_1_5_0 : ∀ I J g, Xb1_1_5_0 I J g = Xcb1_1_5_0 I J g := by
  decide +kernel

theorem hYtabb1_1_5_0 : ∀ I J g, Yb1_1_5_0 I J g = Ycb1_1_5_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb1_1_5_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_1_5
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_1_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Xb1_1_5_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 hfuseZ_1_5 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Xcb1_1_5_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2)) (realRepBasis ((1 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_1_5_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Yb1_1_5_0 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_1_1 hfuseZ_2_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Ycb1_1_5_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2)) (realRepBasis ((1 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_1_5_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 1 1 5).1 (realGauge.gaugeSizeL 1 1 5).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_1_5_0 TL1_1_5 YLb1_1_5_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb1_1_5_1 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 I) (ro (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((1 : ZMod 8) + 5) (ri (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 I) (ri (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 J) g) (fuseCol (1 : ZMod 8) ((1 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb1_1_5_1 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_1 (fuseRow (1 : ZMod 8) (1 : ZMod 8) (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_2_5 (fuseRow ((1 : ZMod 8) + 1) (5 : ZMod 8) (li (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 1) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb1_1_5_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb1_1_5_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb1_1_5_1 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb1_1_5_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_1_5_1 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb1_1_5_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_1_5_1 : ∀ I J g, Xb1_1_5_1 I J g = Xcb1_1_5_1 I J g := by
  decide +kernel

theorem hYtabb1_1_5_1 : ∀ I J g, Yb1_1_5_1 I J g = Ycb1_1_5_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb1_1_5_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_1_5
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_1_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Xb1_1_5_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 hfuseZ_1_5 hfuseZ_1_6 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Xcb1_1_5_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2)) (realRepBasis ((1 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_1_5_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Yb1_1_5_1 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_1_1 hfuseZ_2_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Ycb1_1_5_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2)) (realRepBasis ((1 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_1_5_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 1 1 5).1 (realGauge.gaugeSizeL 1 1 5).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_1_5_1 TL1_1_5 YLb1_1_5_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc1_1_5_0 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 I) (ro (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((1 : ZMod 8) + 5) (ri (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 I) (ri (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 J) g) (fuseCol (1 : ZMod 8) ((1 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc1_1_5_0 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) = (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (1 : ZMod 8)).1 (realSize (1 : ZMod 8) (1 : ZMod 8)).2 (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_5 (fuseRow ((1 : ZMod 8) + 1) (5 : ZMod 8) (li (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 1) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc1_1_5_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc1_1_5_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcc1_1_5_0 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc1_1_5_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_1_5_0 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc1_1_5_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_1_5_0 : ∀ I J g, Xc1_1_5_0 I J g = Xcc1_1_5_0 I J g := by
  decide +kernel

theorem hYtabc1_1_5_0 : ∀ I J g, Yc1_1_5_0 I J g = Ycc1_1_5_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc1_1_5_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_1_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_1_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Xc1_1_5_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 hfuseZ_1_5 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Xcc1_1_5_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2)) (realRepBasis ((1 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_1_5_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Yc1_1_5_0 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_2_5 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Ycc1_1_5_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2)) (realRepBasis ((1 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_1_5_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 1 1 5).1 (realGauge.gaugeSizeL 1 1 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_1_5_0 TL1_1_5 YLc1_1_5_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc1_1_5_1 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 I) (ro (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((1 : ZMod 8) + 5) (ri (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 I) (ri (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 J) g) (fuseCol (1 : ZMod 8) ((1 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc1_1_5_1 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) = (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (1 : ZMod 8)).1 (realSize (1 : ZMod 8) (1 : ZMod 8)).2 (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_5 (fuseRow ((1 : ZMod 8) + 1) (5 : ZMod 8) (li (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 1) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc1_1_5_1 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc1_1_5_1 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]]]

noncomputable def Xcc1_1_5_1 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc1_1_5_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_1_5_1 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc1_1_5_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_1_5_1 : ∀ I J g, Xc1_1_5_1 I J g = Xcc1_1_5_1 I J g := by
  decide +kernel

theorem hYtabc1_1_5_1 : ∀ I J g, Yc1_1_5_1 I J g = Ycc1_1_5_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc1_1_5_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_1_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_1_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Xc1_1_5_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 hfuseZ_1_5 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Xcc1_1_5_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2)) (realRepBasis ((1 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_1_5_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Yc1_1_5_1 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_2_5 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Ycc1_1_5_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2)) (realRepBasis ((1 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_1_5_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 1 1 5).1 (realGauge.gaugeSizeL 1 1 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_1_5_1 TL1_1_5 YLc1_1_5_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc1_1_5_2 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 I) (ro (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((1 : ZMod 8) + 5) (ri (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 I) (ri (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 J) g) (fuseCol (1 : ZMod 8) ((1 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc1_1_5_2 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) = (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (1 : ZMod 8)).1 (realSize (1 : ZMod 8) (1 : ZMod 8)).2 (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_5 (fuseRow ((1 : ZMod 8) + 1) (5 : ZMod 8) (li (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 1) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc1_1_5_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc1_1_5_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0]]]

noncomputable def Xcc1_1_5_2 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc1_1_5_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_1_5_2 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc1_1_5_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_1_5_2 : ∀ I J g, Xc1_1_5_2 I J g = Xcc1_1_5_2 I J g := by
  decide +kernel

theorem hYtabc1_1_5_2 : ∀ I J g, Yc1_1_5_2 I J g = Ycc1_1_5_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc1_1_5_2 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_1_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_1_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Xc1_1_5_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 hfuseZ_1_5 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Xcc1_1_5_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2)) (realRepBasis ((1 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_1_5_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Yc1_1_5_2 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_2_5 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Ycc1_1_5_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2)) (realRepBasis ((1 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_1_5_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 1 1 5).1 (realGauge.gaugeSizeL 1 1 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_1_5_2 TL1_1_5 YLc1_1_5_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc1_1_5_3 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 I) (ro (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((1 : ZMod 8) + 5) (ri (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 I) (ri (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 J) g) (fuseCol (1 : ZMod 8) ((1 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc1_1_5_3 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) = (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (1 : ZMod 8)).1 (realSize (1 : ZMod 8) (1 : ZMod 8)).2 (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_5 (fuseRow ((1 : ZMod 8) + 1) (5 : ZMod 8) (li (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 1) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc1_1_5_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc1_1_5_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]]]

noncomputable def Xcc1_1_5_3 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc1_1_5_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_1_5_3 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc1_1_5_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_1_5_3 : ∀ I J g, Xc1_1_5_3 I J g = Xcc1_1_5_3 I J g := by
  decide +kernel

theorem hYtabc1_1_5_3 : ∀ I J g, Yc1_1_5_3 I J g = Ycc1_1_5_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc1_1_5_3 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_1_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_1_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Xc1_1_5_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 hfuseZ_1_5 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Xcc1_1_5_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2)) (realRepBasis ((1 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_1_5_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Yc1_1_5_3 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_2_5 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Ycc1_1_5_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2)) (realRepBasis ((1 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_1_5_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 1 1 5).1 (realGauge.gaugeSizeL 1 1 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_1_5_3 TL1_1_5 YLc1_1_5_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Xc1_1_5_4 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 I) (ro (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((1 : ZMod 8) + 5) (ri (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 I) (ri (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 J) g) (fuseCol (1 : ZMod 8) ((1 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Yc1_1_5_4 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) = (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (1 : ZMod 8)).1 (realSize (1 : ZMod 8) (1 : ZMod 8)).2 (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_5 (fuseRow ((1 : ZMod 8) + 1) (5 : ZMod 8) (li (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 1) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `4`, pre-tabulated. -/
def XLc1_1_5_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `4`, pre-tabulated. -/
def YLc1_1_5_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc1_1_5_4 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc1_1_5_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_1_5_4 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc1_1_5_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_1_5_4 : ∀ I J g, Xc1_1_5_4 I J g = Xcc1_1_5_4 I J g := by
  decide +kernel

theorem hYtabc1_1_5_4 : ∀ I J g, Yc1_1_5_4 I J g = Ycc1_1_5_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `4`** (Koszul sign `+1`). -/
theorem hintc1_1_5_4 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_1_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_1_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Xc1_1_5_4 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 hfuseZ_1_5 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Xcc1_1_5_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2)) (realRepBasis ((1 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_1_5_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Yc1_1_5_4 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_2_5 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Ycc1_1_5_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2)) (realRepBasis ((1 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_1_5_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 1 1 5).1 (realGauge.gaugeSizeL 1 1 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_1_5_4 TL1_1_5 YLc1_1_5_4 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Xc1_1_5_5 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 I) (ro (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((1 : ZMod 8) + 5) (ri (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 I) (ri (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 J) g) (fuseCol (1 : ZMod 8) ((1 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Yc1_1_5_5 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) = (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (1 : ZMod 8)).1 (realSize (1 : ZMod 8) (1 : ZMod 8)).2 (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_5 (fuseRow ((1 : ZMod 8) + 1) (5 : ZMod 8) (li (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 1) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `5`, pre-tabulated. -/
def XLc1_1_5_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `5`, pre-tabulated. -/
def YLc1_1_5_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc1_1_5_5 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc1_1_5_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_1_5_5 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc1_1_5_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_1_5_5 : ∀ I J g, Xc1_1_5_5 I J g = Xcc1_1_5_5 I J g := by
  decide +kernel

theorem hYtabc1_1_5_5 : ∀ I J g, Yc1_1_5_5 I J g = Ycc1_1_5_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintc1_1_5_5 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_1_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_1_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Xc1_1_5_5 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 hfuseZ_1_5 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Xcc1_1_5_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2)) (realRepBasis ((1 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_1_5_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Yc1_1_5_5 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_2_5 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Ycc1_1_5_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2)) (realRepBasis ((1 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_1_5_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 1 1 5).1 (realGauge.gaugeSizeL 1 1 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_1_5_5 TL1_1_5 YLc1_1_5_5 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Xc1_1_5_6 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 I) (ro (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((1 : ZMod 8) + 5) (ri (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 I) (ri (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 J) g) (fuseCol (1 : ZMod 8) ((1 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Yc1_1_5_6 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) = (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (1 : ZMod 8)).1 (realSize (1 : ZMod 8) (1 : ZMod 8)).2 (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_5 (fuseRow ((1 : ZMod 8) + 1) (5 : ZMod 8) (li (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 1) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `6`, pre-tabulated. -/
def XLc1_1_5_6 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `6`, pre-tabulated. -/
def YLc1_1_5_6 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0]]]

noncomputable def Xcc1_1_5_6 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc1_1_5_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_1_5_6 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc1_1_5_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_1_5_6 : ∀ I J g, Xc1_1_5_6 I J g = Xcc1_1_5_6 I J g := by
  decide +kernel

theorem hYtabc1_1_5_6 : ∀ I J g, Yc1_1_5_6 I J g = Ycc1_1_5_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintc1_1_5_6 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_1_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_1_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Xc1_1_5_6 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 hfuseZ_1_5 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Xcc1_1_5_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2)) (realRepBasis ((1 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_1_5_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Yc1_1_5_6 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_2_5 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Ycc1_1_5_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2)) (realRepBasis ((1 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_1_5_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 1 1 5).1 (realGauge.gaugeSizeL 1 1 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_1_5_6 TL1_1_5 YLc1_1_5_6 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Xc1_1_5_7 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 I) (ro (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((1 : ZMod 8) + 5) (ri (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 I) (ri (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 J) g) (fuseCol (1 : ZMod 8) ((1 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Yc1_1_5_7 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) = (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (1 : ZMod 8)).1 (realSize (1 : ZMod 8) (1 : ZMod 8)).2 (lo (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_5 (fuseRow ((1 : ZMod 8) + 1) (5 : ZMod 8) (li (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 1) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `7`, pre-tabulated. -/
def XLc1_1_5_7 : List (List (List ℤ)) :=
  [[[0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 1], [0, 0]]]

/-- Left route at the `c`-slot generator `7`, pre-tabulated. -/
def YLc1_1_5_7 : List (List (List ℤ)) :=
  [[[0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 1], [0, 0]]]

noncomputable def Xcc1_1_5_7 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc1_1_5_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_1_5_7 : (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc1_1_5_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_1_5_7 : ∀ I J g, Xc1_1_5_7 I J g = Xcc1_1_5_7 I J g := by
  decide +kernel

theorem hYtabc1_1_5_7 : ∀ I J g, Yc1_1_5_7 I J g = Ycc1_1_5_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `7`** (Koszul sign `+1`). -/
theorem hintc1_1_5_7 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_1_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_1_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Xc1_1_5_7 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 hfuseZ_1_5 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Xcc1_1_5_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2)) (realRepBasis ((1 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_1_5_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Yc1_1_5_7 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_2_5 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 5)) Ycc1_1_5_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 5).2)) (realRepBasis ((1 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_1_5_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 1 1 5).1 (realGauge.gaugeSizeL 1 1 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_1_5_7 TL1_1_5 YLc1_1_5_7 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint1_1_5 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T1_1_5
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_1_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hinta1_1_5_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hinta1_1_5_1

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint1_1_5 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T1_1_5
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_1_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hintb1_1_5_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hintb1_1_5_1

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint1_1_5 (i : Fin (realRepDim (5 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) i)) * T1_1_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_1_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h0]; exact hintc1_1_5_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h1]; exact hintc1_1_5_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h2]; exact hintc1_1_5_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h3]; exact hintc1_1_5_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h4]; exact hintc1_1_5_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h5]; exact hintc1_1_5_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h6]; exact hintc1_1_5_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h7]; exact hintc1_1_5_7

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT1_1_5_mem_gInterSpace :
    gtOfT ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 T1_1_5 ∈ gInterSpace ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 hT1_1_5 hAint1_1_5 hBint1_1_5 hCint1_1_5

theorem gtOfT1_1_5_ne_zero : gtOfT ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 T1_1_5 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz1_1_5 T1_1_5_ne_zero

theorem gInterSpace1_1_5_ne_bot : gInterSpace ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT1_1_5_mem_gInterSpace, gtOfT1_1_5_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_1_1_5 : gParity ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) gInterSpace1_1_5_ne_bot).symm

end Triple_1_1_5

/-! ### The triple `(1,1,6)`

`gaugeSizeL = gaugeSizeR = (2,2)`, `dim D_0 = 1`, certgen parity `0`; the unit-slot shortcut: the connector is the identity, so every certificate carries the sign `+1`. -/
section Triple_1_1_6
open Module
theorem hsz1_1_6 : realGauge.gaugeSizeR 1 1 6 = realGauge.gaugeSizeL 1 1 6 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`4 x 4 x 1`). -/
def TL1_1_6 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0]],
   [[0], [1], [0], [0]],
   [[0], [0], [1], [0]],
   [[0], [0], [0], [1]]]

/-- The same literal read at the composite frame `Fin 2 ⊕ Fin 2`. -/
noncomputable def Tc1_1_6 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet TL1_1_6 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_0`. -/
noncomputable def T1_1_6 : ((realGauge.D ((1 : ZMod 8) + 1 + 6)).matrixSuper
    (realGauge.gaugeSizeL 1 1 6).1 (realGauge.gaugeSizeL 1 1 6).2).carrier :=
  matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Tc1_1_6

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT1_1_6 : T1_1_6 ∈ ((realGauge.D ((1 : ZMod 8) + 1 + 6)).matrixSuper
    (realGauge.gaugeSizeL 1 1 6).1 (realGauge.gaugeSizeL 1 1 6).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((1 : ZMod 8) + 1 + 6) Tc1_1_6 0 (by decide)

theorem T1_1_6_ne_zero : T1_1_6 ≠ 0 :=
  matOfCoeff_ne_zero ((1 : ZMod 8) + 1 + 6) Tc1_1_6 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa1_1_6_0 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 I) = (ro (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (6 : ZMod 8)).1 (realSize (1 : ZMod 8) (6 : ZMod 8)).2 (ro (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 I)
          * realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((1 : ZMod 8) + 6) (ri (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 I) (ri (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 J) g) (fuseCol (1 : ZMod 8) ((1 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya1_1_6_0 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_1 (fuseRow (1 : ZMod 8) (1 : ZMod 8) (lo (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (lo (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_2_6 (fuseRow ((1 : ZMod 8) + 1) (6 : ZMod 8) (li (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (li (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 1) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa1_1_6_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0]],
   [[0], [1], [0], [0]],
   [[0], [0], [1], [0]],
   [[0], [0], [0], [1]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa1_1_6_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0]],
   [[0], [1], [0], [0]],
   [[0], [0], [1], [0]],
   [[0], [0], [0], [1]]]

noncomputable def Xca1_1_6_0 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa1_1_6_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_1_6_0 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa1_1_6_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 1 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_1_6_0 : ∀ I J g, Xa1_1_6_0 I J g = Xca1_1_6_0 I J g := by
  decide +kernel

theorem hYtaba1_1_6_0 : ∀ I J g, Ya1_1_6_0 I J g = Yca1_1_6_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta1_1_6_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_1_6
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_1_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Xa1_1_6_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Xca1_1_6_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2)) (realRepBasis ((1 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_1_6_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Ya1_1_6_0 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hfuseZ_1_1 hfuseZ_2_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Yca1_1_6_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2)) (realRepBasis ((1 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_1_6_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 1 + 6) (realGauge.gaugeSizeL 1 1 6).1 (realGauge.gaugeSizeL 1 1 6).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa1_1_6_0 TL1_1_6 YLa1_1_6_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa1_1_6_1 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 I) = (ro (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (6 : ZMod 8)).1 (realSize (1 : ZMod 8) (6 : ZMod 8)).2 (ro (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 I)
          * realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((1 : ZMod 8) + 6) (ri (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 I) (ri (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 J) g) (fuseCol (1 : ZMod 8) ((1 : ZMod 8) + 6) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya1_1_6_1 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_1 (fuseRow (1 : ZMod 8) (1 : ZMod 8) (lo (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (lo (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_2_6 (fuseRow ((1 : ZMod 8) + 1) (6 : ZMod 8) (li (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (li (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 1) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa1_1_6_1 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0]],
   [[0], [0], [0], [1]],
   [[-1], [0], [0], [0]],
   [[0], [-1], [0], [0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa1_1_6_1 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0]],
   [[0], [0], [0], [1]],
   [[-1], [0], [0], [0]],
   [[0], [-1], [0], [0]]]

noncomputable def Xca1_1_6_1 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa1_1_6_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_1_6_1 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa1_1_6_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 1 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_1_6_1 : ∀ I J g, Xa1_1_6_1 I J g = Xca1_1_6_1 I J g := by
  decide +kernel

theorem hYtaba1_1_6_1 : ∀ I J g, Ya1_1_6_1 I J g = Yca1_1_6_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta1_1_6_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_1_6
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_1_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Xa1_1_6_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 hfuseZ_1_7 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Xca1_1_6_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2)) (realRepBasis ((1 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_1_6_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Ya1_1_6_1 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hfuseZ_1_1 hfuseZ_2_6 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Yca1_1_6_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2)) (realRepBasis ((1 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_1_6_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 1 + 6) (realGauge.gaugeSizeL 1 1 6).1 (realGauge.gaugeSizeL 1 1 6).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa1_1_6_1 TL1_1_6 YLa1_1_6_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb1_1_6_0 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_6 (fuseRow (1 : ZMod 8) (6 : ZMod 8) (ro (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 I) (ro (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 J) ee) (fuseCol (1 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((1 : ZMod 8) + 6) (ri (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 I) (ri (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 J) g) (fuseCol (1 : ZMod 8) ((1 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb1_1_6_0 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_1 (fuseRow (1 : ZMod 8) (1 : ZMod 8) (lo (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (lo (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_2_6 (fuseRow ((1 : ZMod 8) + 1) (6 : ZMod 8) (li (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (li (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 1) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb1_1_6_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0]],
   [[0], [1], [0], [0]],
   [[0], [0], [1], [0]],
   [[0], [0], [0], [1]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb1_1_6_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0]],
   [[0], [1], [0], [0]],
   [[0], [0], [1], [0]],
   [[0], [0], [0], [1]]]

noncomputable def Xcb1_1_6_0 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb1_1_6_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_1_6_0 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb1_1_6_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 1 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_1_6_0 : ∀ I J g, Xb1_1_6_0 I J g = Xcb1_1_6_0 I J g := by
  decide +kernel

theorem hYtabb1_1_6_0 : ∀ I J g, Yb1_1_6_0 I J g = Ycb1_1_6_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb1_1_6_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_1_6
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_1_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Xb1_1_6_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 hfuseZ_1_6 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Xcb1_1_6_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2)) (realRepBasis ((1 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_1_6_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Yb1_1_6_0 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hfuseZ_1_1 hfuseZ_2_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Ycb1_1_6_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2)) (realRepBasis ((1 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_1_6_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 1 + 6) (realGauge.gaugeSizeL 1 1 6).1 (realGauge.gaugeSizeL 1 1 6).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_1_6_0 TL1_1_6 YLb1_1_6_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb1_1_6_1 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_6 (fuseRow (1 : ZMod 8) (6 : ZMod 8) (ro (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 I) (ro (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 J) ee) (fuseCol (1 : ZMod 8) (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((1 : ZMod 8) + 6) (ri (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 I) (ri (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 J) g) (fuseCol (1 : ZMod 8) ((1 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb1_1_6_1 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_1 (fuseRow (1 : ZMod 8) (1 : ZMod 8) (lo (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (lo (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_2_6 (fuseRow ((1 : ZMod 8) + 1) (6 : ZMod 8) (li (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (li (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 1) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb1_1_6_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1]],
   [[0], [0], [-1], [0]],
   [[0], [1], [0], [0]],
   [[-1], [0], [0], [0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb1_1_6_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1]],
   [[0], [0], [-1], [0]],
   [[0], [1], [0], [0]],
   [[-1], [0], [0], [0]]]

noncomputable def Xcb1_1_6_1 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb1_1_6_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_1_6_1 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb1_1_6_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 1 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_1_6_1 : ∀ I J g, Xb1_1_6_1 I J g = Xcb1_1_6_1 I J g := by
  decide +kernel

theorem hYtabb1_1_6_1 : ∀ I J g, Yb1_1_6_1 I J g = Ycb1_1_6_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb1_1_6_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_1_6
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_1_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Xb1_1_6_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 hfuseZ_1_6 hfuseZ_1_7 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Xcb1_1_6_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2)) (realRepBasis ((1 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_1_6_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Yb1_1_6_1 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hfuseZ_1_1 hfuseZ_2_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Ycb1_1_6_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2)) (realRepBasis ((1 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_1_6_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 1 + 6) (realGauge.gaugeSizeL 1 1 6).1 (realGauge.gaugeSizeL 1 1 6).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_1_6_1 TL1_1_6 YLb1_1_6_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc1_1_6_0 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_6 (fuseRow (1 : ZMod 8) (6 : ZMod 8) (ro (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 I) (ro (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 J) ee) (fuseCol (1 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((1 : ZMod 8) + 6) (ri (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 I) (ri (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 J) g) (fuseCol (1 : ZMod 8) ((1 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc1_1_6_0 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) = (lo (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (1 : ZMod 8)).1 (realSize (1 : ZMod 8) (1 : ZMod 8)).2 (lo (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_6 (fuseRow ((1 : ZMod 8) + 1) (6 : ZMod 8) (li (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (li (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 1) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc1_1_6_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0]],
   [[0], [1], [0], [0]],
   [[0], [0], [1], [0]],
   [[0], [0], [0], [1]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc1_1_6_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0]],
   [[0], [1], [0], [0]],
   [[0], [0], [1], [0]],
   [[0], [0], [0], [1]]]

noncomputable def Xcc1_1_6_0 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc1_1_6_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_1_6_0 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc1_1_6_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 1 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_1_6_0 : ∀ I J g, Xc1_1_6_0 I J g = Xcc1_1_6_0 I J g := by
  decide +kernel

theorem hYtabc1_1_6_0 : ∀ I J g, Yc1_1_6_0 I J g = Ycc1_1_6_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc1_1_6_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T1_1_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_1_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Xc1_1_6_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 hfuseZ_1_6 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Xcc1_1_6_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2)) (realRepBasis ((1 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_1_6_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Yc1_1_6_0 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hfuseZ_2_6 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Ycc1_1_6_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2)) (realRepBasis ((1 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_1_6_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 1 + 6) (realGauge.gaugeSizeL 1 1 6).1 (realGauge.gaugeSizeL 1 1 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_1_6_0 TL1_1_6 YLc1_1_6_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc1_1_6_1 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_6 (fuseRow (1 : ZMod 8) (6 : ZMod 8) (ro (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 I) (ro (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 J) ee) (fuseCol (1 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((1 : ZMod 8) + 6) (ri (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 I) (ri (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 J) g) (fuseCol (1 : ZMod 8) ((1 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc1_1_6_1 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) = (lo (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (1 : ZMod 8)).1 (realSize (1 : ZMod 8) (1 : ZMod 8)).2 (lo (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_6 (fuseRow ((1 : ZMod 8) + 1) (6 : ZMod 8) (li (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (li (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 1) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc1_1_6_1 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0]],
   [[0], [0], [0], [-1]],
   [[1], [0], [0], [0]],
   [[0], [-1], [0], [0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc1_1_6_1 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0]],
   [[0], [0], [0], [-1]],
   [[1], [0], [0], [0]],
   [[0], [-1], [0], [0]]]

noncomputable def Xcc1_1_6_1 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc1_1_6_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_1_6_1 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc1_1_6_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 1 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_1_6_1 : ∀ I J g, Xc1_1_6_1 I J g = Xcc1_1_6_1 I J g := by
  decide +kernel

theorem hYtabc1_1_6_1 : ∀ I J g, Yc1_1_6_1 I J g = Ycc1_1_6_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc1_1_6_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T1_1_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_1_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Xc1_1_6_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 hfuseZ_1_6 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Xcc1_1_6_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2)) (realRepBasis ((1 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_1_6_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Yc1_1_6_1 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hfuseZ_2_6 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Ycc1_1_6_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2)) (realRepBasis ((1 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_1_6_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 1 + 6) (realGauge.gaugeSizeL 1 1 6).1 (realGauge.gaugeSizeL 1 1 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_1_6_1 TL1_1_6 YLc1_1_6_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc1_1_6_2 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_6 (fuseRow (1 : ZMod 8) (6 : ZMod 8) (ro (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 I) (ro (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 J) ee) (fuseCol (1 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((1 : ZMod 8) + 6) (ri (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 I) (ri (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 J) g) (fuseCol (1 : ZMod 8) ((1 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc1_1_6_2 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) = (lo (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (1 : ZMod 8)).1 (realSize (1 : ZMod 8) (1 : ZMod 8)).2 (lo (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_6 (fuseRow ((1 : ZMod 8) + 1) (6 : ZMod 8) (li (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (li (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 1) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc1_1_6_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1]],
   [[0], [0], [1], [0]],
   [[0], [1], [0], [0]],
   [[1], [0], [0], [0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc1_1_6_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1]],
   [[0], [0], [1], [0]],
   [[0], [1], [0], [0]],
   [[1], [0], [0], [0]]]

noncomputable def Xcc1_1_6_2 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc1_1_6_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_1_6_2 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc1_1_6_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 1 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_1_6_2 : ∀ I J g, Xc1_1_6_2 I J g = Xcc1_1_6_2 I J g := by
  decide +kernel

theorem hYtabc1_1_6_2 : ∀ I J g, Yc1_1_6_2 I J g = Ycc1_1_6_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc1_1_6_2 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T1_1_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_1_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Xc1_1_6_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 hfuseZ_1_6 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Xcc1_1_6_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2)) (realRepBasis ((1 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_1_6_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Yc1_1_6_2 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hfuseZ_2_6 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Ycc1_1_6_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2)) (realRepBasis ((1 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_1_6_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 1 + 6) (realGauge.gaugeSizeL 1 1 6).1 (realGauge.gaugeSizeL 1 1 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_1_6_2 TL1_1_6 YLc1_1_6_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc1_1_6_3 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_6 (fuseRow (1 : ZMod 8) (6 : ZMod 8) (ro (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 I) (ro (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 J) ee) (fuseCol (1 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((1 : ZMod 8) + 6) (ri (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 I) (ri (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 J) g) (fuseCol (1 : ZMod 8) ((1 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc1_1_6_3 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) = (lo (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (1 : ZMod 8)).1 (realSize (1 : ZMod 8) (1 : ZMod 8)).2 (lo (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_6 (fuseRow ((1 : ZMod 8) + 1) (6 : ZMod 8) (li (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (li (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 1) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc1_1_6_3 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0]],
   [[-1], [0], [0], [0]],
   [[0], [0], [0], [1]],
   [[0], [0], [-1], [0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc1_1_6_3 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0]],
   [[-1], [0], [0], [0]],
   [[0], [0], [0], [1]],
   [[0], [0], [-1], [0]]]

noncomputable def Xcc1_1_6_3 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc1_1_6_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_1_6_3 : (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2) → Fin (realRepDim ((1 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc1_1_6_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 1 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_1_6_3 : ∀ I J g, Xc1_1_6_3 I J g = Xcc1_1_6_3 I J g := by
  decide +kernel

theorem hYtabc1_1_6_3 : ∀ I J g, Yc1_1_6_3 I J g = Ycc1_1_6_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc1_1_6_3 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T1_1_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_1_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Xc1_1_6_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 hfuseZ_1_6 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Xcc1_1_6_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2)) (realRepBasis ((1 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_1_6_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Yc1_1_6_3 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hfuseZ_2_6 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 1 + 6)) Ycc1_1_6_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 1 6).2)) (realRepBasis ((1 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_1_6_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 1 + 6) (realGauge.gaugeSizeL 1 1 6).1 (realGauge.gaugeSizeL 1 1 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_1_6_3 TL1_1_6 YLc1_1_6_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint1_1_6 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T1_1_6
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_1_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hinta1_1_6_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hinta1_1_6_1

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint1_1_6 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T1_1_6
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_1_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hintb1_1_6_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hintb1_1_6_1

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint1_1_6 (i : Fin (realRepDim (6 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) i)) * T1_1_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_1_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h0]; exact hintc1_1_6_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h1]; exact hintc1_1_6_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h2]; exact hintc1_1_6_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h3]; exact hintc1_1_6_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT1_1_6_mem_gInterSpace :
    gtOfT ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 T1_1_6 ∈ gInterSpace ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 hT1_1_6 hAint1_1_6 hBint1_1_6 hCint1_1_6

theorem gtOfT1_1_6_ne_zero : gtOfT ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 T1_1_6 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz1_1_6 T1_1_6_ne_zero

theorem gInterSpace1_1_6_ne_bot : gInterSpace ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT1_1_6_mem_gInterSpace, gtOfT1_1_6_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_1_1_6 : gParity ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (1 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) gInterSpace1_1_6_ne_bot).symm

end Triple_1_1_6

/-! ### The triple `(1,2,3)`

`gaugeSizeL = gaugeSizeR = (2,2)`, `dim D_6 = 4`, certgen parity `1`; the transported connector literal. -/
section Triple_1_2_3
open Module
theorem hsz1_2_3 : realGauge.gaugeSizeR 1 2 3 = realGauge.gaugeSizeL 1 2 3 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`4 x 4 x 4`). -/
def TL1_2_3 : List (List (List ℤ)) :=
  [[[0, 1, -1, 0], [0, 1, -1, 0], [1, 0, 0, 1], [-1, 0, 0, -1]],
   [[0, -1, 1, 0], [0, 1, -1, 0], [-1, 0, 0, -1], [-1, 0, 0, -1]],
   [[1, 0, 0, -1], [-1, 0, 0, 1], [0, -1, -1, 0], [0, -1, -1, 0]],
   [[1, 0, 0, -1], [1, 0, 0, -1], [0, -1, -1, 0], [0, 1, 1, 0]]]

/-- The same literal read at the composite frame `Fin 2 ⊕ Fin 2`. -/
noncomputable def Tc1_2_3 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet TL1_2_3 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_6`. -/
noncomputable def T1_2_3 : ((realGauge.D ((1 : ZMod 8) + 2 + 3)).matrixSuper
    (realGauge.gaugeSizeL 1 2 3).1 (realGauge.gaugeSizeL 1 2 3).2).carrier :=
  matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Tc1_2_3

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT1_2_3 : T1_2_3 ∈ ((realGauge.D ((1 : ZMod 8) + 2 + 3)).matrixSuper
    (realGauge.gaugeSizeL 1 2 3).1 (realGauge.gaugeSizeL 1 2 3).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((1 : ZMod 8) + 2 + 3) Tc1_2_3 1 (by decide)

theorem T1_2_3_ne_zero : T1_2_3 ≠ 0 :=
  matOfCoeff_ne_zero ((1 : ZMod 8) + 2 + 3) Tc1_2_3 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨1, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa1_2_3_0 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) = (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (3 : ZMod 8)).1 (realSize (2 : ZMod 8) (3 : ZMod 8)).2 (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I)
          * realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_5 (fuseRow (1 : ZMod 8) ((2 : ZMod 8) + 3) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) g) (fuseCol (1 : ZMod 8) ((2 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya1_2_3_0 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_2 (fuseRow (1 : ZMod 8) (2 : ZMod 8) (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_3_3 (fuseRow ((1 : ZMod 8) + 2) (3 : ZMod 8) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 2) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa1_2_3_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa1_2_3_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xca1_2_3_0 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa1_2_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_2_3_0 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa1_2_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_2_3_0 : ∀ I J g, Xa1_2_3_0 I J g = Xca1_2_3_0 I J g := by
  decide +kernel

theorem hYtaba1_2_3_0 : ∀ I J g, Ya1_2_3_0 I J g = Yca1_2_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta1_2_3_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_2_3
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_2_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xa1_2_3_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xca1_2_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_2_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Ya1_2_3_0 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_1_2 hfuseZ_3_3 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Yca1_2_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_2_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 1 2 3).1 (realGauge.gaugeSizeL 1 2 3).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa1_2_3_0 TL1_2_3 YLa1_2_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa1_2_3_1 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) = (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (3 : ZMod 8)).1 (realSize (2 : ZMod 8) (3 : ZMod 8)).2 (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I)
          * realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_5 (fuseRow (1 : ZMod 8) ((2 : ZMod 8) + 3) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) g) (fuseCol (1 : ZMod 8) ((2 : ZMod 8) + 3) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya1_2_3_1 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_2 (fuseRow (1 : ZMod 8) (2 : ZMod 8) (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_3_3 (fuseRow ((1 : ZMod 8) + 2) (3 : ZMod 8) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 2) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa1_2_3_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa1_2_3_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]]]

noncomputable def Xca1_2_3_1 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa1_2_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_2_3_1 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa1_2_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_2_3_1 : ∀ I J g, Xa1_2_3_1 I J g = Xca1_2_3_1 I J g := by
  decide +kernel

theorem hYtaba1_2_3_1 : ∀ I J g, Ya1_2_3_1 I J g = Yca1_2_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `-1`). -/
theorem hinta1_2_3_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_2_3
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_2_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xa1_2_3_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 hfuseZ_1_5 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xca1_2_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_2_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Ya1_2_3_1 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_1_2 hfuseZ_3_3 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Yca1_2_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_2_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 1 2 3).1 (realGauge.gaugeSizeL 1 2 3).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa1_2_3_1 TL1_2_3 YLa1_2_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb1_2_3_0 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow (1 : ZMod 8) ((2 : ZMod 8) + 3) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) g) (fuseCol (1 : ZMod 8) ((2 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb1_2_3_0 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_2 (fuseRow (1 : ZMod 8) (2 : ZMod 8) (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_3_3 (fuseRow ((1 : ZMod 8) + 2) (3 : ZMod 8) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 2) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb1_2_3_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb1_2_3_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcb1_2_3_0 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb1_2_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_2_3_0 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb1_2_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_2_3_0 : ∀ I J g, Xb1_2_3_0 I J g = Xcb1_2_3_0 I J g := by
  decide +kernel

theorem hYtabb1_2_3_0 : ∀ I J g, Yb1_2_3_0 I J g = Ycb1_2_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb1_2_3_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T1_2_3
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_2_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xb1_2_3_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 hfuseZ_2_3 hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xcb1_2_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_2_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Yb1_2_3_0 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_1_2 hfuseZ_3_3 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Ycb1_2_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_2_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 1 2 3).1 (realGauge.gaugeSizeL 1 2 3).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_2_3_0 TL1_2_3 YLb1_2_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb1_2_3_1 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow (1 : ZMod 8) ((2 : ZMod 8) + 3) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) g) (fuseCol (1 : ZMod 8) ((2 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb1_2_3_1 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_2 (fuseRow (1 : ZMod 8) (2 : ZMod 8) (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_3_3 (fuseRow ((1 : ZMod 8) + 2) (3 : ZMod 8) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 2) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb1_2_3_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb1_2_3_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb1_2_3_1 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb1_2_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_2_3_1 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb1_2_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_2_3_1 : ∀ I J g, Xb1_2_3_1 I J g = Xcb1_2_3_1 I J g := by
  decide +kernel

theorem hYtabb1_2_3_1 : ∀ I J g, Yb1_2_3_1 I J g = Ycb1_2_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintb1_2_3_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T1_2_3
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_2_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xb1_2_3_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 hfuseZ_2_3 hfuseZ_1_5 (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xcb1_2_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_2_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Yb1_2_3_1 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_1_2 hfuseZ_3_3 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Ycb1_2_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_2_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 1 2 3).1 (realGauge.gaugeSizeL 1 2 3).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_2_3_1 TL1_2_3 YLb1_2_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb1_2_3_2 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow (1 : ZMod 8) ((2 : ZMod 8) + 3) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) g) (fuseCol (1 : ZMod 8) ((2 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb1_2_3_2 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_2 (fuseRow (1 : ZMod 8) (2 : ZMod 8) (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_3_3 (fuseRow ((1 : ZMod 8) + 2) (3 : ZMod 8) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 2) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb1_2_3_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb1_2_3_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb1_2_3_2 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb1_2_3_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_2_3_2 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb1_2_3_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_2_3_2 : ∀ I J g, Xb1_2_3_2 I J g = Xcb1_2_3_2 I J g := by
  decide +kernel

theorem hYtabb1_2_3_2 : ∀ I J g, Yb1_2_3_2 I J g = Ycb1_2_3_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintb1_2_3_2 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T1_2_3
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_2_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xb1_2_3_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 hfuseZ_2_3 hfuseZ_1_5 (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xcb1_2_3_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_2_3_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Yb1_2_3_2 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_1_2 hfuseZ_3_3 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Ycb1_2_3_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_2_3_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 1 2 3).1 (realGauge.gaugeSizeL 1 2 3).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_2_3_2 TL1_2_3 YLb1_2_3_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb1_2_3_3 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow (1 : ZMod 8) ((2 : ZMod 8) + 3) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) g) (fuseCol (1 : ZMod 8) ((2 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb1_2_3_3 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_2 (fuseRow (1 : ZMod 8) (2 : ZMod 8) (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_3_3 (fuseRow ((1 : ZMod 8) + 2) (3 : ZMod 8) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 2) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb1_2_3_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb1_2_3_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb1_2_3_3 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb1_2_3_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_2_3_3 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb1_2_3_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_2_3_3 : ∀ I J g, Xb1_2_3_3 I J g = Xcb1_2_3_3 I J g := by
  decide +kernel

theorem hYtabb1_2_3_3 : ∀ I J g, Yb1_2_3_3 I J g = Ycb1_2_3_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb1_2_3_3 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T1_2_3
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_2_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xb1_2_3_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 hfuseZ_2_3 hfuseZ_1_5 (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xcb1_2_3_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_2_3_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Yb1_2_3_3 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_1_2 hfuseZ_3_3 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Ycb1_2_3_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_2_3_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 1 2 3).1 (realGauge.gaugeSizeL 1 2 3).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_2_3_3 TL1_2_3 YLb1_2_3_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc1_2_3_0 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow (1 : ZMod 8) ((2 : ZMod 8) + 3) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) g) (fuseCol (1 : ZMod 8) ((2 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc1_2_3_0 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) = (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (2 : ZMod 8)).1 (realSize (1 : ZMod 8) (2 : ZMod 8)).2 (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_3 (fuseRow ((1 : ZMod 8) + 2) (3 : ZMod 8) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 2) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc1_2_3_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc1_2_3_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcc1_2_3_0 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc1_2_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_2_3_0 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc1_2_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_2_3_0 : ∀ I J g, Xc1_2_3_0 I J g = Xcc1_2_3_0 I J g := by
  decide +kernel

theorem hYtabc1_2_3_0 : ∀ I J g, Yc1_2_3_0 I J g = Ycc1_2_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc1_2_3_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_2_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_2_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xc1_2_3_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 hfuseZ_2_3 hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xcc1_2_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_2_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Yc1_2_3_0 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_3_3 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Ycc1_2_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_2_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 1 2 3).1 (realGauge.gaugeSizeL 1 2 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc1_2_3_0 TL1_2_3 YLc1_2_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc1_2_3_1 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow (1 : ZMod 8) ((2 : ZMod 8) + 3) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) g) (fuseCol (1 : ZMod 8) ((2 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc1_2_3_1 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) = (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (2 : ZMod 8)).1 (realSize (1 : ZMod 8) (2 : ZMod 8)).2 (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_3 (fuseRow ((1 : ZMod 8) + 2) (3 : ZMod 8) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 2) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc1_2_3_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc1_2_3_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc1_2_3_1 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc1_2_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_2_3_1 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc1_2_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_2_3_1 : ∀ I J g, Xc1_2_3_1 I J g = Xcc1_2_3_1 I J g := by
  decide +kernel

theorem hYtabc1_2_3_1 : ∀ I J g, Yc1_2_3_1 I J g = Ycc1_2_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintc1_2_3_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_2_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_2_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xc1_2_3_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 hfuseZ_2_3 hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xcc1_2_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_2_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Yc1_2_3_1 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_3_3 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Ycc1_2_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_2_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 1 2 3).1 (realGauge.gaugeSizeL 1 2 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc1_2_3_1 TL1_2_3 YLc1_2_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc1_2_3_2 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow (1 : ZMod 8) ((2 : ZMod 8) + 3) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) g) (fuseCol (1 : ZMod 8) ((2 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc1_2_3_2 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) = (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (2 : ZMod 8)).1 (realSize (1 : ZMod 8) (2 : ZMod 8)).2 (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_3 (fuseRow ((1 : ZMod 8) + 2) (3 : ZMod 8) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 2) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc1_2_3_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc1_2_3_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1]],
   [[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc1_2_3_2 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc1_2_3_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_2_3_2 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc1_2_3_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_2_3_2 : ∀ I J g, Xc1_2_3_2 I J g = Xcc1_2_3_2 I J g := by
  decide +kernel

theorem hYtabc1_2_3_2 : ∀ I J g, Yc1_2_3_2 I J g = Ycc1_2_3_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintc1_2_3_2 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_2_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_2_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xc1_2_3_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 hfuseZ_2_3 hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xcc1_2_3_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_2_3_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Yc1_2_3_2 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_3_3 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Ycc1_2_3_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_2_3_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 1 2 3).1 (realGauge.gaugeSizeL 1 2 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc1_2_3_2 TL1_2_3 YLc1_2_3_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc1_2_3_3 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow (1 : ZMod 8) ((2 : ZMod 8) + 3) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) g) (fuseCol (1 : ZMod 8) ((2 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc1_2_3_3 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) = (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (2 : ZMod 8)).1 (realSize (1 : ZMod 8) (2 : ZMod 8)).2 (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_3 (fuseRow ((1 : ZMod 8) + 2) (3 : ZMod 8) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 2) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc1_2_3_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc1_2_3_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]]]

noncomputable def Xcc1_2_3_3 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc1_2_3_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_2_3_3 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc1_2_3_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_2_3_3 : ∀ I J g, Xc1_2_3_3 I J g = Xcc1_2_3_3 I J g := by
  decide +kernel

theorem hYtabc1_2_3_3 : ∀ I J g, Yc1_2_3_3 I J g = Ycc1_2_3_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc1_2_3_3 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_2_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_2_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xc1_2_3_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 hfuseZ_2_3 hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xcc1_2_3_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_2_3_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Yc1_2_3_3 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_3_3 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Ycc1_2_3_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_2_3_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 1 2 3).1 (realGauge.gaugeSizeL 1 2 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc1_2_3_3 TL1_2_3 YLc1_2_3_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Xc1_2_3_4 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow (1 : ZMod 8) ((2 : ZMod 8) + 3) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) g) (fuseCol (1 : ZMod 8) ((2 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Yc1_2_3_4 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) = (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (2 : ZMod 8)).1 (realSize (1 : ZMod 8) (2 : ZMod 8)).2 (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_3 (fuseRow ((1 : ZMod 8) + 2) (3 : ZMod 8) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 2) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `4`, pre-tabulated. -/
def XLc1_2_3_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1]],
   [[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `4`, pre-tabulated. -/
def YLc1_2_3_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc1_2_3_4 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc1_2_3_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_2_3_4 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc1_2_3_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_2_3_4 : ∀ I J g, Xc1_2_3_4 I J g = Xcc1_2_3_4 I J g := by
  decide +kernel

theorem hYtabc1_2_3_4 : ∀ I J g, Yc1_2_3_4 I J g = Ycc1_2_3_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `4`** (Koszul sign `-1`). -/
theorem hintc1_2_3_4 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_2_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_2_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xc1_2_3_4 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 hfuseZ_2_3 hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xcc1_2_3_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_2_3_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Yc1_2_3_4 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_3_3 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Ycc1_2_3_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_2_3_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 1 2 3).1 (realGauge.gaugeSizeL 1 2 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc1_2_3_4 TL1_2_3 YLc1_2_3_4 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Xc1_2_3_5 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow (1 : ZMod 8) ((2 : ZMod 8) + 3) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) g) (fuseCol (1 : ZMod 8) ((2 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Yc1_2_3_5 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) = (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (2 : ZMod 8)).1 (realSize (1 : ZMod 8) (2 : ZMod 8)).2 (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_3 (fuseRow ((1 : ZMod 8) + 2) (3 : ZMod 8) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 2) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `5`, pre-tabulated. -/
def XLc1_2_3_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `5`, pre-tabulated. -/
def YLc1_2_3_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc1_2_3_5 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc1_2_3_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_2_3_5 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc1_2_3_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_2_3_5 : ∀ I J g, Xc1_2_3_5 I J g = Xcc1_2_3_5 I J g := by
  decide +kernel

theorem hYtabc1_2_3_5 : ∀ I J g, Yc1_2_3_5 I J g = Ycc1_2_3_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintc1_2_3_5 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_2_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_2_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xc1_2_3_5 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 hfuseZ_2_3 hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xcc1_2_3_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_2_3_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Yc1_2_3_5 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_3_3 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Ycc1_2_3_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_2_3_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 1 2 3).1 (realGauge.gaugeSizeL 1 2 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc1_2_3_5 TL1_2_3 YLc1_2_3_5 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Xc1_2_3_6 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow (1 : ZMod 8) ((2 : ZMod 8) + 3) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) g) (fuseCol (1 : ZMod 8) ((2 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Yc1_2_3_6 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) = (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (2 : ZMod 8)).1 (realSize (1 : ZMod 8) (2 : ZMod 8)).2 (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_3 (fuseRow ((1 : ZMod 8) + 2) (3 : ZMod 8) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 2) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `6`, pre-tabulated. -/
def XLc1_2_3_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `6`, pre-tabulated. -/
def YLc1_2_3_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1]]]

noncomputable def Xcc1_2_3_6 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc1_2_3_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_2_3_6 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc1_2_3_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_2_3_6 : ∀ I J g, Xc1_2_3_6 I J g = Xcc1_2_3_6 I J g := by
  decide +kernel

theorem hYtabc1_2_3_6 : ∀ I J g, Yc1_2_3_6 I J g = Ycc1_2_3_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintc1_2_3_6 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_2_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_2_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xc1_2_3_6 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 hfuseZ_2_3 hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xcc1_2_3_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_2_3_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Yc1_2_3_6 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_3_3 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Ycc1_2_3_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_2_3_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 1 2 3).1 (realGauge.gaugeSizeL 1 2 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc1_2_3_6 TL1_2_3 YLc1_2_3_6 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Xc1_2_3_7 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) (ro (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow (1 : ZMod 8) ((2 : ZMod 8) + 3) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 I) (ri (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 J) g) (fuseCol (1 : ZMod 8) ((2 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Yc1_2_3_7 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) = (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (2 : ZMod 8)).1 (realSize (1 : ZMod 8) (2 : ZMod 8)).2 (lo (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_3 (fuseRow ((1 : ZMod 8) + 2) (3 : ZMod 8) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 2) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `7`, pre-tabulated. -/
def XLc1_2_3_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `7`, pre-tabulated. -/
def YLc1_2_3_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc1_2_3_7 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc1_2_3_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_2_3_7 : (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc1_2_3_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_2_3_7 : ∀ I J g, Xc1_2_3_7 I J g = Xcc1_2_3_7 I J g := by
  decide +kernel

theorem hYtabc1_2_3_7 : ∀ I J g, Yc1_2_3_7 I J g = Ycc1_2_3_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `7`** (Koszul sign `-1`). -/
theorem hintc1_2_3_7 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_2_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_2_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xc1_2_3_7 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 hfuseZ_2_3 hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Xcc1_2_3_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_2_3_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Yc1_2_3_7 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_3_3 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 3)) Ycc1_2_3_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 3).2)) (realRepBasis ((1 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_2_3_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 1 2 3).1 (realGauge.gaugeSizeL 1 2 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc1_2_3_7 TL1_2_3 YLc1_2_3_7 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint1_2_3 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T1_2_3
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T1_2_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hinta1_2_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hinta1_2_3_1

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint1_2_3 (i : Fin (realRepDim (2 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) i)) * T1_2_3
      = ((sgn (realRepBasisParity (2 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T1_2_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h0]; exact hintb1_2_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h1]; exact hintb1_2_3_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h2]; exact hintb1_2_3_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h3]; exact hintb1_2_3_3

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint1_2_3 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T1_2_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T1_2_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hintc1_2_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hintc1_2_3_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hintc1_2_3_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hintc1_2_3_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hintc1_2_3_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hintc1_2_3_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hintc1_2_3_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hintc1_2_3_7

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT1_2_3_mem_gInterSpace :
    gtOfT ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 T1_2_3 ∈ gInterSpace ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 hT1_2_3 hAint1_2_3 hBint1_2_3 hCint1_2_3

theorem gtOfT1_2_3_ne_zero : gtOfT ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 T1_2_3 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz1_2_3 T1_2_3_ne_zero

theorem gInterSpace1_2_3_ne_bot : gInterSpace ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT1_2_3_mem_gInterSpace, gtOfT1_2_3_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_1_2_3 : gParity ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) gInterSpace1_2_3_ne_bot).symm

end Triple_1_2_3

/-! ### The triple `(1,2,4)`

`gaugeSizeL = gaugeSizeR = (2,2)`, `dim D_7 = 2`, certgen parity `0`; the transported connector literal. -/
section Triple_1_2_4
open Module
theorem hsz1_2_4 : realGauge.gaugeSizeR 1 2 4 = realGauge.gaugeSizeL 1 2 4 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`4 x 4 x 2`). -/
def TL1_2_4 : List (List (List ℤ)) :=
  [[[1, 0], [1, 0], [0, 1], [0, 1]],
   [[-1, 0], [1, 0], [0, -1], [0, 1]],
   [[0, -1], [0, 1], [1, 0], [-1, 0]],
   [[0, -1], [0, -1], [1, 0], [1, 0]]]

/-- The same literal read at the composite frame `Fin 2 ⊕ Fin 2`. -/
noncomputable def Tc1_2_4 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun r s g => coeffGet TL1_2_4 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_7`. -/
noncomputable def T1_2_4 : ((realGauge.D ((1 : ZMod 8) + 2 + 4)).matrixSuper
    (realGauge.gaugeSizeL 1 2 4).1 (realGauge.gaugeSizeL 1 2 4).2).carrier :=
  matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Tc1_2_4

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT1_2_4 : T1_2_4 ∈ ((realGauge.D ((1 : ZMod 8) + 2 + 4)).matrixSuper
    (realGauge.gaugeSizeL 1 2 4).1 (realGauge.gaugeSizeL 1 2 4).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((1 : ZMod 8) + 2 + 4) Tc1_2_4 0 (by decide)

theorem T1_2_4_ne_zero : T1_2_4 ≠ 0 :=
  matOfCoeff_ne_zero ((1 : ZMod 8) + 2 + 4) Tc1_2_4 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa1_2_4_0 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 I) = (ro (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (4 : ZMod 8)).1 (realSize (2 : ZMod 8) (4 : ZMod 8)).2 (ro (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 I)
          * realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((2 : ZMod 8) + 4) (ri (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 I) (ri (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 J) g) (fuseCol (1 : ZMod 8) ((2 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya1_2_4_0 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_2 (fuseRow (1 : ZMod 8) (2 : ZMod 8) (lo (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_3_4 (fuseRow ((1 : ZMod 8) + 2) (4 : ZMod 8) (li (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 2) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa1_2_4_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa1_2_4_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xca1_2_4_0 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa1_2_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_2_4_0 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa1_2_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_2_4_0 : ∀ I J g, Xa1_2_4_0 I J g = Xca1_2_4_0 I J g := by
  decide +kernel

theorem hYtaba1_2_4_0 : ∀ I J g, Ya1_2_4_0 I J g = Yca1_2_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta1_2_4_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_2_4
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_2_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Xa1_2_4_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Xca1_2_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2)) (realRepBasis ((1 : ZMod 8) + 2 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_2_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Ya1_2_4_0 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hfuseZ_1_2 hfuseZ_3_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Yca1_2_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2)) (realRepBasis ((1 : ZMod 8) + 2 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_2_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 2 + 4) (realGauge.gaugeSizeL 1 2 4).1 (realGauge.gaugeSizeL 1 2 4).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa1_2_4_0 TL1_2_4 YLa1_2_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa1_2_4_1 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 I) = (ro (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (4 : ZMod 8)).1 (realSize (2 : ZMod 8) (4 : ZMod 8)).2 (ro (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 I)
          * realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((2 : ZMod 8) + 4) (ri (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 I) (ri (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 J) g) (fuseCol (1 : ZMod 8) ((2 : ZMod 8) + 4) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya1_2_4_1 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_2 (fuseRow (1 : ZMod 8) (2 : ZMod 8) (lo (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_3_4 (fuseRow ((1 : ZMod 8) + 2) (4 : ZMod 8) (li (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 2) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa1_2_4_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa1_2_4_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 1], [0, 0]]]

noncomputable def Xca1_2_4_1 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa1_2_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_2_4_1 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa1_2_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_2_4_1 : ∀ I J g, Xa1_2_4_1 I J g = Xca1_2_4_1 I J g := by
  decide +kernel

theorem hYtaba1_2_4_1 : ∀ I J g, Ya1_2_4_1 I J g = Yca1_2_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta1_2_4_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_2_4
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_2_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Xa1_2_4_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 hfuseZ_1_6 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Xca1_2_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2)) (realRepBasis ((1 : ZMod 8) + 2 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_2_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Ya1_2_4_1 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hfuseZ_1_2 hfuseZ_3_4 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Yca1_2_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2)) (realRepBasis ((1 : ZMod 8) + 2 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_2_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 2 + 4) (realGauge.gaugeSizeL 1 2 4).1 (realGauge.gaugeSizeL 1 2 4).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa1_2_4_1 TL1_2_4 YLa1_2_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb1_2_4_0 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 I) (ro (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((2 : ZMod 8) + 4) (ri (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 I) (ri (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 J) g) (fuseCol (1 : ZMod 8) ((2 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb1_2_4_0 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_2 (fuseRow (1 : ZMod 8) (2 : ZMod 8) (lo (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_3_4 (fuseRow ((1 : ZMod 8) + 2) (4 : ZMod 8) (li (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 2) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb1_2_4_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb1_2_4_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcb1_2_4_0 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb1_2_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_2_4_0 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb1_2_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_2_4_0 : ∀ I J g, Xb1_2_4_0 I J g = Xcb1_2_4_0 I J g := by
  decide +kernel

theorem hYtabb1_2_4_0 : ∀ I J g, Yb1_2_4_0 I J g = Ycb1_2_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb1_2_4_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T1_2_4
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_2_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Xb1_2_4_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 hfuseZ_2_4 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Xcb1_2_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2)) (realRepBasis ((1 : ZMod 8) + 2 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_2_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Yb1_2_4_0 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hfuseZ_1_2 hfuseZ_3_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Ycb1_2_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2)) (realRepBasis ((1 : ZMod 8) + 2 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_2_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 2 + 4) (realGauge.gaugeSizeL 1 2 4).1 (realGauge.gaugeSizeL 1 2 4).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_2_4_0 TL1_2_4 YLb1_2_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb1_2_4_1 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 I) (ro (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((2 : ZMod 8) + 4) (ri (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 I) (ri (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 J) g) (fuseCol (1 : ZMod 8) ((2 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb1_2_4_1 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_2 (fuseRow (1 : ZMod 8) (2 : ZMod 8) (lo (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_3_4 (fuseRow ((1 : ZMod 8) + 2) (4 : ZMod 8) (li (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 2) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb1_2_4_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 1], [0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb1_2_4_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb1_2_4_1 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb1_2_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_2_4_1 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb1_2_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_2_4_1 : ∀ I J g, Xb1_2_4_1 I J g = Xcb1_2_4_1 I J g := by
  decide +kernel

theorem hYtabb1_2_4_1 : ∀ I J g, Yb1_2_4_1 I J g = Ycb1_2_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb1_2_4_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T1_2_4
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_2_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Xb1_2_4_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 hfuseZ_2_4 hfuseZ_1_6 (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Xcb1_2_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2)) (realRepBasis ((1 : ZMod 8) + 2 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_2_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Yb1_2_4_1 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hfuseZ_1_2 hfuseZ_3_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Ycb1_2_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2)) (realRepBasis ((1 : ZMod 8) + 2 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_2_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 2 + 4) (realGauge.gaugeSizeL 1 2 4).1 (realGauge.gaugeSizeL 1 2 4).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_2_4_1 TL1_2_4 YLb1_2_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb1_2_4_2 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 I) (ro (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((2 : ZMod 8) + 4) (ri (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 I) (ri (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 J) g) (fuseCol (1 : ZMod 8) ((2 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb1_2_4_2 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_2 (fuseRow (1 : ZMod 8) (2 : ZMod 8) (lo (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_3_4 (fuseRow ((1 : ZMod 8) + 2) (4 : ZMod 8) (li (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 2) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb1_2_4_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb1_2_4_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0]]]

noncomputable def Xcb1_2_4_2 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb1_2_4_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_2_4_2 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb1_2_4_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_2_4_2 : ∀ I J g, Xb1_2_4_2 I J g = Xcb1_2_4_2 I J g := by
  decide +kernel

theorem hYtabb1_2_4_2 : ∀ I J g, Yb1_2_4_2 I J g = Ycb1_2_4_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb1_2_4_2 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T1_2_4
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_2_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Xb1_2_4_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 hfuseZ_2_4 hfuseZ_1_6 (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Xcb1_2_4_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2)) (realRepBasis ((1 : ZMod 8) + 2 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_2_4_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Yb1_2_4_2 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hfuseZ_1_2 hfuseZ_3_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Ycb1_2_4_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2)) (realRepBasis ((1 : ZMod 8) + 2 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_2_4_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 2 + 4) (realGauge.gaugeSizeL 1 2 4).1 (realGauge.gaugeSizeL 1 2 4).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_2_4_2 TL1_2_4 YLb1_2_4_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb1_2_4_3 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 I) (ro (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((2 : ZMod 8) + 4) (ri (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 I) (ri (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 J) g) (fuseCol (1 : ZMod 8) ((2 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb1_2_4_3 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_2 (fuseRow (1 : ZMod 8) (2 : ZMod 8) (lo (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_3_4 (fuseRow ((1 : ZMod 8) + 2) (4 : ZMod 8) (li (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 2) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb1_2_4_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb1_2_4_3 : List (List (List ℤ)) :=
  [[[0, 0], [-1, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0]]]

noncomputable def Xcb1_2_4_3 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb1_2_4_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_2_4_3 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb1_2_4_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_2_4_3 : ∀ I J g, Xb1_2_4_3 I J g = Xcb1_2_4_3 I J g := by
  decide +kernel

theorem hYtabb1_2_4_3 : ∀ I J g, Yb1_2_4_3 I J g = Ycb1_2_4_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb1_2_4_3 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T1_2_4
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_2_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Xb1_2_4_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 hfuseZ_2_4 hfuseZ_1_6 (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Xcb1_2_4_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2)) (realRepBasis ((1 : ZMod 8) + 2 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_2_4_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Yb1_2_4_3 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hfuseZ_1_2 hfuseZ_3_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Ycb1_2_4_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2)) (realRepBasis ((1 : ZMod 8) + 2 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_2_4_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 2 + 4) (realGauge.gaugeSizeL 1 2 4).1 (realGauge.gaugeSizeL 1 2 4).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_2_4_3 TL1_2_4 YLb1_2_4_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc1_2_4_0 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 I) (ro (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((2 : ZMod 8) + 4) (ri (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 I) (ri (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 J) g) (fuseCol (1 : ZMod 8) ((2 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc1_2_4_0 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) I) = (lo (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (2 : ZMod 8)).1 (realSize (1 : ZMod 8) (2 : ZMod 8)).2 (lo (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_4 (fuseRow ((1 : ZMod 8) + 2) (4 : ZMod 8) (li (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 2) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc1_2_4_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc1_2_4_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcc1_2_4_0 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc1_2_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_2_4_0 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc1_2_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_2_4_0 : ∀ I J g, Xc1_2_4_0 I J g = Xcc1_2_4_0 I J g := by
  decide +kernel

theorem hYtabc1_2_4_0 : ∀ I J g, Yc1_2_4_0 I J g = Ycc1_2_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc1_2_4_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_2_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_2_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Xc1_2_4_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 hfuseZ_2_4 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Xcc1_2_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2)) (realRepBasis ((1 : ZMod 8) + 2 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_2_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Yc1_2_4_0 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hfuseZ_3_4 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Ycc1_2_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2)) (realRepBasis ((1 : ZMod 8) + 2 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_2_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 2 + 4) (realGauge.gaugeSizeL 1 2 4).1 (realGauge.gaugeSizeL 1 2 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_2_4_0 TL1_2_4 YLc1_2_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc1_2_4_1 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 I) (ro (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((2 : ZMod 8) + 4) (ri (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 I) (ri (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 J) g) (fuseCol (1 : ZMod 8) ((2 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc1_2_4_1 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) I) = (lo (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (2 : ZMod 8)).1 (realSize (1 : ZMod 8) (2 : ZMod 8)).2 (lo (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_4 (fuseRow ((1 : ZMod 8) + 2) (4 : ZMod 8) (li (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 2) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc1_2_4_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc1_2_4_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]]]

noncomputable def Xcc1_2_4_1 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc1_2_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_2_4_1 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc1_2_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_2_4_1 : ∀ I J g, Xc1_2_4_1 I J g = Xcc1_2_4_1 I J g := by
  decide +kernel

theorem hYtabc1_2_4_1 : ∀ I J g, Yc1_2_4_1 I J g = Ycc1_2_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc1_2_4_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_2_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_2_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Xc1_2_4_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 hfuseZ_2_4 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Xcc1_2_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2)) (realRepBasis ((1 : ZMod 8) + 2 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_2_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Yc1_2_4_1 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hfuseZ_3_4 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Ycc1_2_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2)) (realRepBasis ((1 : ZMod 8) + 2 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_2_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 2 + 4) (realGauge.gaugeSizeL 1 2 4).1 (realGauge.gaugeSizeL 1 2 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_2_4_1 TL1_2_4 YLc1_2_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc1_2_4_2 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 I) (ro (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((2 : ZMod 8) + 4) (ri (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 I) (ri (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 J) g) (fuseCol (1 : ZMod 8) ((2 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc1_2_4_2 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) I) = (lo (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (2 : ZMod 8)).1 (realSize (1 : ZMod 8) (2 : ZMod 8)).2 (lo (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_4 (fuseRow ((1 : ZMod 8) + 2) (4 : ZMod 8) (li (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 2) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc1_2_4_2 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc1_2_4_2 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0]]]

noncomputable def Xcc1_2_4_2 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc1_2_4_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_2_4_2 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc1_2_4_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_2_4_2 : ∀ I J g, Xc1_2_4_2 I J g = Xcc1_2_4_2 I J g := by
  decide +kernel

theorem hYtabc1_2_4_2 : ∀ I J g, Yc1_2_4_2 I J g = Ycc1_2_4_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc1_2_4_2 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_2_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_2_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Xc1_2_4_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 hfuseZ_2_4 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Xcc1_2_4_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2)) (realRepBasis ((1 : ZMod 8) + 2 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_2_4_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Yc1_2_4_2 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hfuseZ_3_4 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Ycc1_2_4_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2)) (realRepBasis ((1 : ZMod 8) + 2 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_2_4_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 2 + 4) (realGauge.gaugeSizeL 1 2 4).1 (realGauge.gaugeSizeL 1 2 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_2_4_2 TL1_2_4 YLc1_2_4_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc1_2_4_3 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 I) (ro (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((2 : ZMod 8) + 4) (ri (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 I) (ri (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 J) g) (fuseCol (1 : ZMod 8) ((2 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc1_2_4_3 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) I) = (lo (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (2 : ZMod 8)).1 (realSize (1 : ZMod 8) (2 : ZMod 8)).2 (lo (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_4 (fuseRow ((1 : ZMod 8) + 2) (4 : ZMod 8) (li (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 2) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc1_2_4_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc1_2_4_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc1_2_4_3 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc1_2_4_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_2_4_3 : (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2) → Fin (realRepDim ((1 : ZMod 8) + 2 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc1_2_4_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_2_4_3 : ∀ I J g, Xc1_2_4_3 I J g = Xcc1_2_4_3 I J g := by
  decide +kernel

theorem hYtabc1_2_4_3 : ∀ I J g, Yc1_2_4_3 I J g = Ycc1_2_4_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc1_2_4_3 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_2_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_2_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Xc1_2_4_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 hfuseZ_2_4 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Xcc1_2_4_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2)) (realRepBasis ((1 : ZMod 8) + 2 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_2_4_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Yc1_2_4_3 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hfuseZ_3_4 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 2 + 4)) Ycc1_2_4_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 2 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 2 4).2)) (realRepBasis ((1 : ZMod 8) + 2 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_2_4_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 2 + 4) (realGauge.gaugeSizeL 1 2 4).1 (realGauge.gaugeSizeL 1 2 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_2_4_3 TL1_2_4 YLc1_2_4_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint1_2_4 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T1_2_4
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_2_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hinta1_2_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hinta1_2_4_1

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint1_2_4 (i : Fin (realRepDim (2 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (2 : ZMod 8) i)) * T1_2_4
      = ((sgn (realRepBasisParity (2 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_2_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (2 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h0]; exact hintb1_2_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h1]; exact hintb1_2_4_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h2]; exact hintb1_2_4_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h3]; exact hintb1_2_4_3

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint1_2_4 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T1_2_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_2_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hintc1_2_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hintc1_2_4_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hintc1_2_4_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hintc1_2_4_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT1_2_4_mem_gInterSpace :
    gtOfT ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 T1_2_4 ∈ gInterSpace ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 hT1_2_4 hAint1_2_4 hBint1_2_4 hCint1_2_4

theorem gtOfT1_2_4_ne_zero : gtOfT ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 T1_2_4 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) hsz1_2_4 T1_2_4_ne_zero

theorem gInterSpace1_2_4_ne_bot : gInterSpace ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT1_2_4_mem_gInterSpace, gtOfT1_2_4_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_1_2_4 : gParity ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (1 : ZMod 8) (2 : ZMod 8) (4 : ZMod 8) gInterSpace1_2_4_ne_bot).symm

end Triple_1_2_4

/-! ### The triple `(1,3,6)`

`gaugeSizeL = gaugeSizeR = (2,2)`, `dim D_2 = 4`, certgen parity `0`; the transported connector literal. -/
section Triple_1_3_6
open Module
theorem hsz1_3_6 : realGauge.gaugeSizeR 1 3 6 = realGauge.gaugeSizeL 1 3 6 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`4 x 4 x 4`). -/
def TL1_3_6 : List (List (List ℤ)) :=
  [[[1, 0, 0, -1], [-1, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 1], [1, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 1], [-1, 0, 0, -1]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, -1], [1, 0, 0, -1]]]

/-- The same literal read at the composite frame `Fin 2 ⊕ Fin 2`. -/
noncomputable def Tc1_3_6 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet TL1_3_6 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_2`. -/
noncomputable def T1_3_6 : ((realGauge.D ((1 : ZMod 8) + 3 + 6)).matrixSuper
    (realGauge.gaugeSizeL 1 3 6).1 (realGauge.gaugeSizeL 1 3 6).2).carrier :=
  matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Tc1_3_6

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT1_3_6 : T1_3_6 ∈ ((realGauge.D ((1 : ZMod 8) + 3 + 6)).matrixSuper
    (realGauge.gaugeSizeL 1 3 6).1 (realGauge.gaugeSizeL 1 3 6).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((1 : ZMod 8) + 3 + 6) Tc1_3_6 0 (by decide)

theorem T1_3_6_ne_zero : T1_3_6 ≠ 0 :=
  matOfCoeff_ne_zero ((1 : ZMod 8) + 3 + 6) Tc1_3_6 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa1_3_6_0 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) = (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (6 : ZMod 8)).1 (realSize (3 : ZMod 8) (6 : ZMod 8)).2 (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I)
          * realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 6) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya1_3_6_0 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_6 (fuseRow ((1 : ZMod 8) + 3) (6 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa1_3_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa1_3_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xca1_3_6_0 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa1_3_6_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_3_6_0 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa1_3_6_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_3_6_0 : ∀ I J g, Xa1_3_6_0 I J g = Xca1_3_6_0 I J g := by
  decide +kernel

theorem hYtaba1_3_6_0 : ∀ I J g, Ya1_3_6_0 I J g = Yca1_3_6_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta1_3_6_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_3_6
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xa1_3_6_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 hfuseZ_1_1 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xca1_3_6_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_3_6_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Ya1_3_6_0 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_1_3 hfuseZ_4_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Yca1_3_6_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_3_6_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 1 3 6).1 (realGauge.gaugeSizeL 1 3 6).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa1_3_6_0 TL1_3_6 YLa1_3_6_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa1_3_6_1 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) = (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (6 : ZMod 8)).1 (realSize (3 : ZMod 8) (6 : ZMod 8)).2 (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I)
          * realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 6) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 6) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya1_3_6_1 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_6 (fuseRow ((1 : ZMod 8) + 3) (6 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa1_3_6_1 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa1_3_6_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]]]

noncomputable def Xca1_3_6_1 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa1_3_6_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_3_6_1 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa1_3_6_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_3_6_1 : ∀ I J g, Xa1_3_6_1 I J g = Xca1_3_6_1 I J g := by
  decide +kernel

theorem hYtaba1_3_6_1 : ∀ I J g, Ya1_3_6_1 I J g = Yca1_3_6_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta1_3_6_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_3_6
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xa1_3_6_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 hfuseZ_1_1 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xca1_3_6_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_3_6_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Ya1_3_6_1 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_1_3 hfuseZ_4_6 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Yca1_3_6_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_3_6_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 1 3 6).1 (realGauge.gaugeSizeL 1 3 6).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa1_3_6_1 TL1_3_6 YLa1_3_6_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb1_3_6_0 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 6) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb1_3_6_0 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_6 (fuseRow ((1 : ZMod 8) + 3) (6 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb1_3_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb1_3_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcb1_3_6_0 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_6_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_6_0 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_6_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_6_0 : ∀ I J g, Xb1_3_6_0 I J g = Xcb1_3_6_0 I J g := by
  decide +kernel

theorem hYtabb1_3_6_0 : ∀ I J g, Yb1_3_6_0 I J g = Ycb1_3_6_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb1_3_6_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xb1_3_6_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 hfuseZ_3_6 hfuseZ_1_1 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xcb1_3_6_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_6_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Yb1_3_6_0 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_1_3 hfuseZ_4_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Ycb1_3_6_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_6_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 1 3 6).1 (realGauge.gaugeSizeL 1 3 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_3_6_0 TL1_3_6 YLb1_3_6_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb1_3_6_1 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 6) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb1_3_6_1 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_6 (fuseRow ((1 : ZMod 8) + 3) (6 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb1_3_6_1 : List (List (List ℤ)) :=
  [[[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb1_3_6_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb1_3_6_1 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_6_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_6_1 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_6_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_6_1 : ∀ I J g, Xb1_3_6_1 I J g = Xcb1_3_6_1 I J g := by
  decide +kernel

theorem hYtabb1_3_6_1 : ∀ I J g, Yb1_3_6_1 I J g = Ycb1_3_6_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb1_3_6_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xb1_3_6_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 hfuseZ_3_6 hfuseZ_1_1 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xcb1_3_6_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_6_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Yb1_3_6_1 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_1_3 hfuseZ_4_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Ycb1_3_6_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_6_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 1 3 6).1 (realGauge.gaugeSizeL 1 3 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_3_6_1 TL1_3_6 YLb1_3_6_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb1_3_6_2 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 6) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb1_3_6_2 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_6 (fuseRow ((1 : ZMod 8) + 3) (6 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb1_3_6_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb1_3_6_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb1_3_6_2 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_6_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_6_2 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_6_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_6_2 : ∀ I J g, Xb1_3_6_2 I J g = Xcb1_3_6_2 I J g := by
  decide +kernel

theorem hYtabb1_3_6_2 : ∀ I J g, Yb1_3_6_2 I J g = Ycb1_3_6_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb1_3_6_2 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xb1_3_6_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 hfuseZ_3_6 hfuseZ_1_1 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xcb1_3_6_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_6_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Yb1_3_6_2 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_1_3 hfuseZ_4_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Ycb1_3_6_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_6_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 1 3 6).1 (realGauge.gaugeSizeL 1 3 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_3_6_2 TL1_3_6 YLb1_3_6_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb1_3_6_3 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 6) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb1_3_6_3 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_6 (fuseRow ((1 : ZMod 8) + 3) (6 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb1_3_6_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb1_3_6_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb1_3_6_3 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_6_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_6_3 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_6_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_6_3 : ∀ I J g, Xb1_3_6_3 I J g = Xcb1_3_6_3 I J g := by
  decide +kernel

theorem hYtabb1_3_6_3 : ∀ I J g, Yb1_3_6_3 I J g = Ycb1_3_6_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb1_3_6_3 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xb1_3_6_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 hfuseZ_3_6 hfuseZ_1_1 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xcb1_3_6_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_6_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Yb1_3_6_3 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_1_3 hfuseZ_4_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Ycb1_3_6_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_6_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 1 3 6).1 (realGauge.gaugeSizeL 1 3 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_3_6_3 TL1_3_6 YLb1_3_6_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Xb1_3_6_4 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 6) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Yb1_3_6_4 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_6 (fuseRow ((1 : ZMod 8) + 3) (6 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `4`, pre-tabulated. -/
def XLb1_3_6_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `4`, pre-tabulated. -/
def YLb1_3_6_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb1_3_6_4 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_6_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_6_4 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_6_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_6_4 : ∀ I J g, Xb1_3_6_4 I J g = Xcb1_3_6_4 I J g := by
  decide +kernel

theorem hYtabb1_3_6_4 : ∀ I J g, Yb1_3_6_4 I J g = Ycb1_3_6_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `4`** (Koszul sign `+1`). -/
theorem hintb1_3_6_4 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xb1_3_6_4 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 hfuseZ_3_6 hfuseZ_1_1 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xcb1_3_6_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_6_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Yb1_3_6_4 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_1_3 hfuseZ_4_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Ycb1_3_6_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_6_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 1 3 6).1 (realGauge.gaugeSizeL 1 3 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_3_6_4 TL1_3_6 YLb1_3_6_4 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Xb1_3_6_5 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 6) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Yb1_3_6_5 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_6 (fuseRow ((1 : ZMod 8) + 3) (6 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `5`, pre-tabulated. -/
def XLb1_3_6_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `5`, pre-tabulated. -/
def YLb1_3_6_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb1_3_6_5 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_6_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_6_5 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_6_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_6_5 : ∀ I J g, Xb1_3_6_5 I J g = Xcb1_3_6_5 I J g := by
  decide +kernel

theorem hYtabb1_3_6_5 : ∀ I J g, Yb1_3_6_5 I J g = Ycb1_3_6_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintb1_3_6_5 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xb1_3_6_5 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 hfuseZ_3_6 hfuseZ_1_1 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xcb1_3_6_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_6_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Yb1_3_6_5 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_1_3 hfuseZ_4_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Ycb1_3_6_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_6_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 1 3 6).1 (realGauge.gaugeSizeL 1 3 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_3_6_5 TL1_3_6 YLb1_3_6_5 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Xb1_3_6_6 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 6) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Yb1_3_6_6 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_6 (fuseRow ((1 : ZMod 8) + 3) (6 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `6`, pre-tabulated. -/
def XLb1_3_6_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `6`, pre-tabulated. -/
def YLb1_3_6_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1]]]

noncomputable def Xcb1_3_6_6 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_6_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_6_6 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_6_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_6_6 : ∀ I J g, Xb1_3_6_6 I J g = Xcb1_3_6_6 I J g := by
  decide +kernel

theorem hYtabb1_3_6_6 : ∀ I J g, Yb1_3_6_6 I J g = Ycb1_3_6_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintb1_3_6_6 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xb1_3_6_6 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 hfuseZ_3_6 hfuseZ_1_1 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xcb1_3_6_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_6_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Yb1_3_6_6 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_1_3 hfuseZ_4_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Ycb1_3_6_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_6_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 1 3 6).1 (realGauge.gaugeSizeL 1 3 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_3_6_6 TL1_3_6 YLb1_3_6_6 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Xb1_3_6_7 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 6) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Yb1_3_6_7 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_6 (fuseRow ((1 : ZMod 8) + 3) (6 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `7`, pre-tabulated. -/
def XLb1_3_6_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `7`, pre-tabulated. -/
def YLb1_3_6_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]]]

noncomputable def Xcb1_3_6_7 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_6_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_6_7 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_6_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_6_7 : ∀ I J g, Xb1_3_6_7 I J g = Xcb1_3_6_7 I J g := by
  decide +kernel

theorem hYtabb1_3_6_7 : ∀ I J g, Yb1_3_6_7 I J g = Ycb1_3_6_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `7`** (Koszul sign `+1`). -/
theorem hintb1_3_6_7 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xb1_3_6_7 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 hfuseZ_3_6 hfuseZ_1_1 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xcb1_3_6_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_6_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Yb1_3_6_7 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_1_3 hfuseZ_4_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Ycb1_3_6_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_6_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 1 3 6).1 (realGauge.gaugeSizeL 1 3 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_3_6_7 TL1_3_6 YLb1_3_6_7 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc1_3_6_0 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 6) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc1_3_6_0 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) = (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_6 (fuseRow ((1 : ZMod 8) + 3) (6 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc1_3_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc1_3_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcc1_3_6_0 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc1_3_6_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_3_6_0 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc1_3_6_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_3_6_0 : ∀ I J g, Xc1_3_6_0 I J g = Xcc1_3_6_0 I J g := by
  decide +kernel

theorem hYtabc1_3_6_0 : ∀ I J g, Yc1_3_6_0 I J g = Ycc1_3_6_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc1_3_6_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T1_3_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xc1_3_6_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 hfuseZ_3_6 hfuseZ_1_1 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xcc1_3_6_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_3_6_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Yc1_3_6_0 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_4_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Ycc1_3_6_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_3_6_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 1 3 6).1 (realGauge.gaugeSizeL 1 3 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_3_6_0 TL1_3_6 YLc1_3_6_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc1_3_6_1 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 6) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc1_3_6_1 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) = (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_6 (fuseRow ((1 : ZMod 8) + 3) (6 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc1_3_6_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc1_3_6_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc1_3_6_1 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc1_3_6_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_3_6_1 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc1_3_6_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_3_6_1 : ∀ I J g, Xc1_3_6_1 I J g = Xcc1_3_6_1 I J g := by
  decide +kernel

theorem hYtabc1_3_6_1 : ∀ I J g, Yc1_3_6_1 I J g = Ycc1_3_6_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc1_3_6_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T1_3_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xc1_3_6_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 hfuseZ_3_6 hfuseZ_1_1 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xcc1_3_6_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_3_6_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Yc1_3_6_1 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_4_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Ycc1_3_6_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_3_6_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 1 3 6).1 (realGauge.gaugeSizeL 1 3 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_3_6_1 TL1_3_6 YLc1_3_6_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc1_3_6_2 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 6) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc1_3_6_2 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) = (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_6 (fuseRow ((1 : ZMod 8) + 3) (6 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc1_3_6_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc1_3_6_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc1_3_6_2 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc1_3_6_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_3_6_2 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc1_3_6_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_3_6_2 : ∀ I J g, Xc1_3_6_2 I J g = Xcc1_3_6_2 I J g := by
  decide +kernel

theorem hYtabc1_3_6_2 : ∀ I J g, Yc1_3_6_2 I J g = Ycc1_3_6_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc1_3_6_2 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T1_3_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xc1_3_6_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 hfuseZ_3_6 hfuseZ_1_1 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xcc1_3_6_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_3_6_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Yc1_3_6_2 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_4_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Ycc1_3_6_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_3_6_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 1 3 6).1 (realGauge.gaugeSizeL 1 3 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_3_6_2 TL1_3_6 YLc1_3_6_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc1_3_6_3 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) (ro (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 6) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 I) (ri (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc1_3_6_3 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) = (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (lo (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_6 (fuseRow ((1 : ZMod 8) + 3) (6 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc1_3_6_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc1_3_6_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]]]

noncomputable def Xcc1_3_6_3 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc1_3_6_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_3_6_3 : (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc1_3_6_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_3_6_3 : ∀ I J g, Xc1_3_6_3 I J g = Xcc1_3_6_3 I J g := by
  decide +kernel

theorem hYtabc1_3_6_3 : ∀ I J g, Yc1_3_6_3 I J g = Ycc1_3_6_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc1_3_6_3 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T1_3_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xc1_3_6_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 hfuseZ_3_6 hfuseZ_1_1 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Xcc1_3_6_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_3_6_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Yc1_3_6_3 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_4_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 6)) Ycc1_3_6_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 6).2)) (realRepBasis ((1 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_3_6_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 1 3 6).1 (realGauge.gaugeSizeL 1 3 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_3_6_3 TL1_3_6 YLc1_3_6_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint1_3_6 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T1_3_6
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_3_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hinta1_3_6_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hinta1_3_6_1

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint1_3_6 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T1_3_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_3_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hintb1_3_6_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hintb1_3_6_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hintb1_3_6_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hintb1_3_6_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hintb1_3_6_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hintb1_3_6_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hintb1_3_6_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hintb1_3_6_7

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint1_3_6 (i : Fin (realRepDim (6 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) i)) * T1_3_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_3_6 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h0]; exact hintc1_3_6_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h1]; exact hintc1_3_6_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h2]; exact hintc1_3_6_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h3]; exact hintc1_3_6_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT1_3_6_mem_gInterSpace :
    gtOfT ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 T1_3_6 ∈ gInterSpace ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 hT1_3_6 hAint1_3_6 hBint1_3_6 hCint1_3_6

theorem gtOfT1_3_6_ne_zero : gtOfT ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 T1_3_6 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz1_3_6 T1_3_6_ne_zero

theorem gInterSpace1_3_6_ne_bot : gInterSpace ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT1_3_6_mem_gInterSpace, gtOfT1_3_6_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_1_3_6 : gParity ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) gInterSpace1_3_6_ne_bot).symm

end Triple_1_3_6

/-! ### The triple `(1,4,2)`

`gaugeSizeL = gaugeSizeR = (2,2)`, `dim D_7 = 2`, certgen parity `1`; the transported connector literal. -/
section Triple_1_4_2
open Module
theorem hsz1_4_2 : realGauge.gaugeSizeR 1 4 2 = realGauge.gaugeSizeL 1 4 2 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`4 x 4 x 2`). -/
def TL1_4_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 1], [-1, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [-1, 0]],
   [[1, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [1, 0], [0, 1], [0, 0]]]

/-- The same literal read at the composite frame `Fin 2 ⊕ Fin 2`. -/
noncomputable def Tc1_4_2 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet TL1_4_2 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_7`. -/
noncomputable def T1_4_2 : ((realGauge.D ((1 : ZMod 8) + 4 + 2)).matrixSuper
    (realGauge.gaugeSizeL 1 4 2).1 (realGauge.gaugeSizeL 1 4 2).2).carrier :=
  matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Tc1_4_2

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT1_4_2 : T1_4_2 ∈ ((realGauge.D ((1 : ZMod 8) + 4 + 2)).matrixSuper
    (realGauge.gaugeSizeL 1 4 2).1 (realGauge.gaugeSizeL 1 4 2).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((1 : ZMod 8) + 4 + 2) Tc1_4_2 1 (by decide)

theorem T1_4_2_ne_zero : T1_4_2 ≠ 0 :=
  matOfCoeff_ne_zero ((1 : ZMod 8) + 4 + 2) Tc1_4_2 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨1, by decide⟩) ⟨1, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa1_4_2_0 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 I) = (ro (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (2 : ZMod 8)).1 (realSize (4 : ZMod 8) (2 : ZMod 8)).2 (ro (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 I)
          * realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 2) (ri (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 I) (ri (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya1_4_2_0 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow ((1 : ZMod 8) + 4) (2 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa1_4_2_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa1_4_2_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xca1_4_2_0 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa1_4_2_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_4_2_0 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa1_4_2_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_4_2_0 : ∀ I J g, Xa1_4_2_0 I J g = Xca1_4_2_0 I J g := by
  decide +kernel

theorem hYtaba1_4_2_0 : ∀ I J g, Ya1_4_2_0 I J g = Yca1_4_2_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta1_4_2_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_4_2
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_4_2 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Xa1_4_2_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Xca1_4_2_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2)) (realRepBasis ((1 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_4_2_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Ya1_4_2_0 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_1_4 hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Yca1_4_2_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2)) (realRepBasis ((1 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_4_2_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 1 4 2).1 (realGauge.gaugeSizeL 1 4 2).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa1_4_2_0 TL1_4_2 YLa1_4_2_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa1_4_2_1 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 I) = (ro (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (2 : ZMod 8)).1 (realSize (4 : ZMod 8) (2 : ZMod 8)).2 (ro (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 I)
          * realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 2) (ri (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 I) (ri (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 2) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya1_4_2_1 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow ((1 : ZMod 8) + 4) (2 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa1_4_2_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa1_4_2_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 1], [0, 0]]]

noncomputable def Xca1_4_2_1 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa1_4_2_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_4_2_1 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa1_4_2_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_4_2_1 : ∀ I J g, Xa1_4_2_1 I J g = Xca1_4_2_1 I J g := by
  decide +kernel

theorem hYtaba1_4_2_1 : ∀ I J g, Ya1_4_2_1 I J g = Yca1_4_2_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `-1`). -/
theorem hinta1_4_2_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_4_2
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_4_2 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Xa1_4_2_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 hfuseZ_1_6 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Xca1_4_2_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2)) (realRepBasis ((1 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_4_2_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Ya1_4_2_1 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_1_4 hfuseZ_5_2 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Yca1_4_2_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2)) (realRepBasis ((1 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_4_2_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 1 4 2).1 (realGauge.gaugeSizeL 1 4 2).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa1_4_2_1 TL1_4_2 YLa1_4_2_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb1_4_2_0 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 I) (ro (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 2) (ri (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 I) (ri (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb1_4_2_0 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow ((1 : ZMod 8) + 4) (2 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb1_4_2_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb1_4_2_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcb1_4_2_0 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb1_4_2_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_4_2_0 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb1_4_2_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_4_2_0 : ∀ I J g, Xb1_4_2_0 I J g = Xcb1_4_2_0 I J g := by
  decide +kernel

theorem hYtabb1_4_2_0 : ∀ I J g, Yb1_4_2_0 I J g = Ycb1_4_2_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb1_4_2_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_4_2
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_4_2 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Xb1_4_2_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 hfuseZ_4_2 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Xcb1_4_2_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2)) (realRepBasis ((1 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_4_2_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Yb1_4_2_0 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_1_4 hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Ycb1_4_2_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2)) (realRepBasis ((1 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_4_2_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 1 4 2).1 (realGauge.gaugeSizeL 1 4 2).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_4_2_0 TL1_4_2 YLb1_4_2_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb1_4_2_1 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 I) (ro (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 2) (ri (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 I) (ri (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb1_4_2_1 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow ((1 : ZMod 8) + 4) (2 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb1_4_2_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb1_4_2_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]]]

noncomputable def Xcb1_4_2_1 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb1_4_2_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_4_2_1 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb1_4_2_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_4_2_1 : ∀ I J g, Xb1_4_2_1 I J g = Xcb1_4_2_1 I J g := by
  decide +kernel

theorem hYtabb1_4_2_1 : ∀ I J g, Yb1_4_2_1 I J g = Ycb1_4_2_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb1_4_2_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_4_2
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_4_2 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Xb1_4_2_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 hfuseZ_4_2 hfuseZ_1_6 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Xcb1_4_2_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2)) (realRepBasis ((1 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_4_2_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Yb1_4_2_1 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_1_4 hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Ycb1_4_2_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2)) (realRepBasis ((1 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_4_2_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 1 4 2).1 (realGauge.gaugeSizeL 1 4 2).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_4_2_1 TL1_4_2 YLb1_4_2_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb1_4_2_2 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 I) (ro (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 2) (ri (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 I) (ri (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb1_4_2_2 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow ((1 : ZMod 8) + 4) (2 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb1_4_2_2 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb1_4_2_2 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0]]]

noncomputable def Xcb1_4_2_2 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb1_4_2_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_4_2_2 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb1_4_2_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_4_2_2 : ∀ I J g, Xb1_4_2_2 I J g = Xcb1_4_2_2 I J g := by
  decide +kernel

theorem hYtabb1_4_2_2 : ∀ I J g, Yb1_4_2_2 I J g = Ycb1_4_2_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb1_4_2_2 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_4_2
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_4_2 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Xb1_4_2_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 hfuseZ_4_2 hfuseZ_1_6 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Xcb1_4_2_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2)) (realRepBasis ((1 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_4_2_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Yb1_4_2_2 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_1_4 hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Ycb1_4_2_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2)) (realRepBasis ((1 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_4_2_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 1 4 2).1 (realGauge.gaugeSizeL 1 4 2).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_4_2_2 TL1_4_2 YLb1_4_2_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb1_4_2_3 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 I) (ro (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 2) (ri (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 I) (ri (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb1_4_2_3 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow ((1 : ZMod 8) + 4) (2 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb1_4_2_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb1_4_2_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb1_4_2_3 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb1_4_2_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_4_2_3 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb1_4_2_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_4_2_3 : ∀ I J g, Xb1_4_2_3 I J g = Xcb1_4_2_3 I J g := by
  decide +kernel

theorem hYtabb1_4_2_3 : ∀ I J g, Yb1_4_2_3 I J g = Ycb1_4_2_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb1_4_2_3 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_4_2
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_4_2 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Xb1_4_2_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 hfuseZ_4_2 hfuseZ_1_6 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Xcb1_4_2_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2)) (realRepBasis ((1 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_4_2_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Yb1_4_2_3 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_1_4 hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Ycb1_4_2_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2)) (realRepBasis ((1 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_4_2_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 1 4 2).1 (realGauge.gaugeSizeL 1 4 2).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_4_2_3 TL1_4_2 YLb1_4_2_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc1_4_2_0 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 I) (ro (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 2) (ri (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 I) (ri (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc1_4_2_0 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) = (lo (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (4 : ZMod 8)).1 (realSize (1 : ZMod 8) (4 : ZMod 8)).2 (lo (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_2 (fuseRow ((1 : ZMod 8) + 4) (2 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc1_4_2_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc1_4_2_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcc1_4_2_0 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc1_4_2_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_4_2_0 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc1_4_2_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_4_2_0 : ∀ I J g, Xc1_4_2_0 I J g = Xcc1_4_2_0 I J g := by
  decide +kernel

theorem hYtabc1_4_2_0 : ∀ I J g, Yc1_4_2_0 I J g = Ycc1_4_2_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc1_4_2_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T1_4_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_4_2 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Xc1_4_2_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 hfuseZ_4_2 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Xcc1_4_2_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2)) (realRepBasis ((1 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_4_2_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Yc1_4_2_0 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Ycc1_4_2_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2)) (realRepBasis ((1 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_4_2_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 1 4 2).1 (realGauge.gaugeSizeL 1 4 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc1_4_2_0 TL1_4_2 YLc1_4_2_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc1_4_2_1 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 I) (ro (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 2) (ri (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 I) (ri (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc1_4_2_1 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) = (lo (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (4 : ZMod 8)).1 (realSize (1 : ZMod 8) (4 : ZMod 8)).2 (lo (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_2 (fuseRow ((1 : ZMod 8) + 4) (2 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc1_4_2_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 1], [0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc1_4_2_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0]]]

noncomputable def Xcc1_4_2_1 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc1_4_2_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_4_2_1 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc1_4_2_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_4_2_1 : ∀ I J g, Xc1_4_2_1 I J g = Xcc1_4_2_1 I J g := by
  decide +kernel

theorem hYtabc1_4_2_1 : ∀ I J g, Yc1_4_2_1 I J g = Ycc1_4_2_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintc1_4_2_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T1_4_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_4_2 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Xc1_4_2_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 hfuseZ_4_2 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Xcc1_4_2_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2)) (realRepBasis ((1 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_4_2_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Yc1_4_2_1 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Ycc1_4_2_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2)) (realRepBasis ((1 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_4_2_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 1 4 2).1 (realGauge.gaugeSizeL 1 4 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc1_4_2_1 TL1_4_2 YLc1_4_2_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc1_4_2_2 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 I) (ro (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 2) (ri (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 I) (ri (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc1_4_2_2 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) = (lo (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (4 : ZMod 8)).1 (realSize (1 : ZMod 8) (4 : ZMod 8)).2 (lo (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_2 (fuseRow ((1 : ZMod 8) + 4) (2 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc1_4_2_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc1_4_2_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc1_4_2_2 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc1_4_2_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_4_2_2 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc1_4_2_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_4_2_2 : ∀ I J g, Xc1_4_2_2 I J g = Xcc1_4_2_2 I J g := by
  decide +kernel

theorem hYtabc1_4_2_2 : ∀ I J g, Yc1_4_2_2 I J g = Ycc1_4_2_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintc1_4_2_2 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T1_4_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_4_2 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Xc1_4_2_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 hfuseZ_4_2 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Xcc1_4_2_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2)) (realRepBasis ((1 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_4_2_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Yc1_4_2_2 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Ycc1_4_2_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2)) (realRepBasis ((1 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_4_2_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 1 4 2).1 (realGauge.gaugeSizeL 1 4 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc1_4_2_2 TL1_4_2 YLc1_4_2_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc1_4_2_3 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 I) (ro (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 2) (ri (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 I) (ri (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc1_4_2_3 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) = (lo (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (4 : ZMod 8)).1 (realSize (1 : ZMod 8) (4 : ZMod 8)).2 (lo (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_2 (fuseRow ((1 : ZMod 8) + 4) (2 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc1_4_2_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc1_4_2_3 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]]]

noncomputable def Xcc1_4_2_3 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc1_4_2_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_4_2_3 : (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc1_4_2_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_4_2_3 : ∀ I J g, Xc1_4_2_3 I J g = Xcc1_4_2_3 I J g := by
  decide +kernel

theorem hYtabc1_4_2_3 : ∀ I J g, Yc1_4_2_3 I J g = Ycc1_4_2_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc1_4_2_3 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T1_4_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_4_2 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Xc1_4_2_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 hfuseZ_4_2 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Xcc1_4_2_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2)) (realRepBasis ((1 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_4_2_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Yc1_4_2_3 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 2)) Ycc1_4_2_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 2).2)) (realRepBasis ((1 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_4_2_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 1 4 2).1 (realGauge.gaugeSizeL 1 4 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc1_4_2_3 TL1_4_2 YLc1_4_2_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint1_4_2 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T1_4_2
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T1_4_2 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hinta1_4_2_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hinta1_4_2_1

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint1_4_2 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T1_4_2
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T1_4_2 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hintb1_4_2_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hintb1_4_2_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hintb1_4_2_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hintb1_4_2_3

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint1_4_2 (i : Fin (realRepDim (2 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) i)) * T1_4_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T1_4_2 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h0]; exact hintc1_4_2_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h1]; exact hintc1_4_2_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h2]; exact hintc1_4_2_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h3]; exact hintc1_4_2_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT1_4_2_mem_gInterSpace :
    gtOfT ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 T1_4_2 ∈ gInterSpace ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 hT1_4_2 hAint1_4_2 hBint1_4_2 hCint1_4_2

theorem gtOfT1_4_2_ne_zero : gtOfT ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 T1_4_2 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz1_4_2 T1_4_2_ne_zero

theorem gInterSpace1_4_2_ne_bot : gInterSpace ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT1_4_2_mem_gInterSpace, gtOfT1_4_2_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_1_4_2 : gParity ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) gInterSpace1_4_2_ne_bot).symm

end Triple_1_4_2

/-! ### The triple `(1,5,4)`

`gaugeSizeL = gaugeSizeR = (2,2)`, `dim D_2 = 4`, certgen parity `0`; the transported connector literal. -/
section Triple_1_5_4
open Module
theorem hsz1_5_4 : realGauge.gaugeSizeR 1 5 4 = realGauge.gaugeSizeL 1 5 4 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`4 x 4 x 4`). -/
def TL1_5_4 : List (List (List ℤ)) :=
  [[[1, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 1, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, -1], [0, -1, 1, 0], [0, 0, 0, 0]],
   [[0, -1, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 1]],
   [[0, 0, 0, 0], [0, 1, -1, 0], [1, 0, 0, 1], [0, 0, 0, 0]]]

/-- The same literal read at the composite frame `Fin 2 ⊕ Fin 2`. -/
noncomputable def Tc1_5_4 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet TL1_5_4 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_2`. -/
noncomputable def T1_5_4 : ((realGauge.D ((1 : ZMod 8) + 5 + 4)).matrixSuper
    (realGauge.gaugeSizeL 1 5 4).1 (realGauge.gaugeSizeL 1 5 4).2).carrier :=
  matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Tc1_5_4

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT1_5_4 : T1_5_4 ∈ ((realGauge.D ((1 : ZMod 8) + 5 + 4)).matrixSuper
    (realGauge.gaugeSizeL 1 5 4).1 (realGauge.gaugeSizeL 1 5 4).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((1 : ZMod 8) + 5 + 4) Tc1_5_4 0 (by decide)

theorem T1_5_4_ne_zero : T1_5_4 ≠ 0 :=
  matOfCoeff_ne_zero ((1 : ZMod 8) + 5 + 4) Tc1_5_4 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa1_5_4_0 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) = (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (4 : ZMod 8)).1 (realSize (5 : ZMod 8) (4 : ZMod 8)).2 (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I)
          * realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 4) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya1_5_4_0 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_4 (fuseRow ((1 : ZMod 8) + 5) (4 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa1_5_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa1_5_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xca1_5_4_0 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa1_5_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_5_4_0 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa1_5_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_5_4_0 : ∀ I J g, Xa1_5_4_0 I J g = Xca1_5_4_0 I J g := by
  decide +kernel

theorem hYtaba1_5_4_0 : ∀ I J g, Ya1_5_4_0 I J g = Yca1_5_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta1_5_4_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_5_4
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xa1_5_4_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 hfuseZ_1_1 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xca1_5_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_5_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Ya1_5_4_0 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_1_5 hfuseZ_6_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Yca1_5_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_5_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 1 5 4).1 (realGauge.gaugeSizeL 1 5 4).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa1_5_4_0 TL1_5_4 YLa1_5_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa1_5_4_1 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) = (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (4 : ZMod 8)).1 (realSize (5 : ZMod 8) (4 : ZMod 8)).2 (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I)
          * realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 4) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 4) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya1_5_4_1 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_4 (fuseRow ((1 : ZMod 8) + 5) (4 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa1_5_4_1 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa1_5_4_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca1_5_4_1 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa1_5_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_5_4_1 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa1_5_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_5_4_1 : ∀ I J g, Xa1_5_4_1 I J g = Xca1_5_4_1 I J g := by
  decide +kernel

theorem hYtaba1_5_4_1 : ∀ I J g, Ya1_5_4_1 I J g = Yca1_5_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta1_5_4_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_5_4
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xa1_5_4_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 hfuseZ_1_1 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xca1_5_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_5_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Ya1_5_4_1 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_1_5 hfuseZ_6_4 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Yca1_5_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_5_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 1 5 4).1 (realGauge.gaugeSizeL 1 5 4).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa1_5_4_1 TL1_5_4 YLa1_5_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb1_5_4_0 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 4) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb1_5_4_0 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_4 (fuseRow ((1 : ZMod 8) + 5) (4 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb1_5_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb1_5_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcb1_5_4_0 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb1_5_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_5_4_0 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb1_5_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_5_4_0 : ∀ I J g, Xb1_5_4_0 I J g = Xcb1_5_4_0 I J g := by
  decide +kernel

theorem hYtabb1_5_4_0 : ∀ I J g, Yb1_5_4_0 I J g = Ycb1_5_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb1_5_4_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_5_4
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xb1_5_4_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 hfuseZ_5_4 hfuseZ_1_1 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xcb1_5_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_5_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Yb1_5_4_0 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_1_5 hfuseZ_6_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Ycb1_5_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_5_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 1 5 4).1 (realGauge.gaugeSizeL 1 5 4).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_5_4_0 TL1_5_4 YLb1_5_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb1_5_4_1 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 4) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb1_5_4_1 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_4 (fuseRow ((1 : ZMod 8) + 5) (4 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb1_5_4_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb1_5_4_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb1_5_4_1 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb1_5_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_5_4_1 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb1_5_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_5_4_1 : ∀ I J g, Xb1_5_4_1 I J g = Xcb1_5_4_1 I J g := by
  decide +kernel

theorem hYtabb1_5_4_1 : ∀ I J g, Yb1_5_4_1 I J g = Ycb1_5_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb1_5_4_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_5_4
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xb1_5_4_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 hfuseZ_5_4 hfuseZ_1_1 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xcb1_5_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_5_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Yb1_5_4_1 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_1_5 hfuseZ_6_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Ycb1_5_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_5_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 1 5 4).1 (realGauge.gaugeSizeL 1 5 4).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_5_4_1 TL1_5_4 YLb1_5_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb1_5_4_2 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 4) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb1_5_4_2 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_4 (fuseRow ((1 : ZMod 8) + 5) (4 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb1_5_4_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb1_5_4_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb1_5_4_2 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb1_5_4_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_5_4_2 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb1_5_4_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_5_4_2 : ∀ I J g, Xb1_5_4_2 I J g = Xcb1_5_4_2 I J g := by
  decide +kernel

theorem hYtabb1_5_4_2 : ∀ I J g, Yb1_5_4_2 I J g = Ycb1_5_4_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb1_5_4_2 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_5_4
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xb1_5_4_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 hfuseZ_5_4 hfuseZ_1_1 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xcb1_5_4_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_5_4_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Yb1_5_4_2 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_1_5 hfuseZ_6_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Ycb1_5_4_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_5_4_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 1 5 4).1 (realGauge.gaugeSizeL 1 5 4).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_5_4_2 TL1_5_4 YLb1_5_4_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb1_5_4_3 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 4) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb1_5_4_3 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_4 (fuseRow ((1 : ZMod 8) + 5) (4 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb1_5_4_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0]],
   [[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb1_5_4_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]]]

noncomputable def Xcb1_5_4_3 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb1_5_4_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_5_4_3 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb1_5_4_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_5_4_3 : ∀ I J g, Xb1_5_4_3 I J g = Xcb1_5_4_3 I J g := by
  decide +kernel

theorem hYtabb1_5_4_3 : ∀ I J g, Yb1_5_4_3 I J g = Ycb1_5_4_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb1_5_4_3 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_5_4
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xb1_5_4_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 hfuseZ_5_4 hfuseZ_1_1 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xcb1_5_4_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_5_4_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Yb1_5_4_3 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_1_5 hfuseZ_6_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Ycb1_5_4_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_5_4_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 1 5 4).1 (realGauge.gaugeSizeL 1 5 4).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_5_4_3 TL1_5_4 YLb1_5_4_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Xb1_5_4_4 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 4) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Yb1_5_4_4 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_4 (fuseRow ((1 : ZMod 8) + 5) (4 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `4`, pre-tabulated. -/
def XLb1_5_4_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `4`, pre-tabulated. -/
def YLb1_5_4_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb1_5_4_4 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb1_5_4_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_5_4_4 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb1_5_4_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_5_4_4 : ∀ I J g, Xb1_5_4_4 I J g = Xcb1_5_4_4 I J g := by
  decide +kernel

theorem hYtabb1_5_4_4 : ∀ I J g, Yb1_5_4_4 I J g = Ycb1_5_4_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `4`** (Koszul sign `+1`). -/
theorem hintb1_5_4_4 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_5_4
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xb1_5_4_4 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 hfuseZ_5_4 hfuseZ_1_1 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xcb1_5_4_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_5_4_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Yb1_5_4_4 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_1_5 hfuseZ_6_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Ycb1_5_4_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_5_4_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 1 5 4).1 (realGauge.gaugeSizeL 1 5 4).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_5_4_4 TL1_5_4 YLb1_5_4_4 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Xb1_5_4_5 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 4) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Yb1_5_4_5 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_4 (fuseRow ((1 : ZMod 8) + 5) (4 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `5`, pre-tabulated. -/
def XLb1_5_4_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `5`, pre-tabulated. -/
def YLb1_5_4_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]]]

noncomputable def Xcb1_5_4_5 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb1_5_4_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_5_4_5 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb1_5_4_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_5_4_5 : ∀ I J g, Xb1_5_4_5 I J g = Xcb1_5_4_5 I J g := by
  decide +kernel

theorem hYtabb1_5_4_5 : ∀ I J g, Yb1_5_4_5 I J g = Ycb1_5_4_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintb1_5_4_5 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_5_4
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xb1_5_4_5 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 hfuseZ_5_4 hfuseZ_1_1 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xcb1_5_4_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_5_4_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Yb1_5_4_5 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_1_5 hfuseZ_6_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Ycb1_5_4_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_5_4_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 1 5 4).1 (realGauge.gaugeSizeL 1 5 4).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_5_4_5 TL1_5_4 YLb1_5_4_5 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Xb1_5_4_6 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 4) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Yb1_5_4_6 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_4 (fuseRow ((1 : ZMod 8) + 5) (4 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `6`, pre-tabulated. -/
def XLb1_5_4_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `6`, pre-tabulated. -/
def YLb1_5_4_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb1_5_4_6 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb1_5_4_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_5_4_6 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb1_5_4_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_5_4_6 : ∀ I J g, Xb1_5_4_6 I J g = Xcb1_5_4_6 I J g := by
  decide +kernel

theorem hYtabb1_5_4_6 : ∀ I J g, Yb1_5_4_6 I J g = Ycb1_5_4_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintb1_5_4_6 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_5_4
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xb1_5_4_6 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 hfuseZ_5_4 hfuseZ_1_1 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xcb1_5_4_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_5_4_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Yb1_5_4_6 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_1_5 hfuseZ_6_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Ycb1_5_4_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_5_4_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 1 5 4).1 (realGauge.gaugeSizeL 1 5 4).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_5_4_6 TL1_5_4 YLb1_5_4_6 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Xb1_5_4_7 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 4) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Yb1_5_4_7 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_4 (fuseRow ((1 : ZMod 8) + 5) (4 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `7`, pre-tabulated. -/
def XLb1_5_4_7 : List (List (List ℤ)) :=
  [[[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]]]

/-- Left route at the `b`-slot generator `7`, pre-tabulated. -/
def YLb1_5_4_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb1_5_4_7 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb1_5_4_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_5_4_7 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb1_5_4_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_5_4_7 : ∀ I J g, Xb1_5_4_7 I J g = Xcb1_5_4_7 I J g := by
  decide +kernel

theorem hYtabb1_5_4_7 : ∀ I J g, Yb1_5_4_7 I J g = Ycb1_5_4_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `7`** (Koszul sign `+1`). -/
theorem hintb1_5_4_7 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_5_4
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xb1_5_4_7 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 hfuseZ_5_4 hfuseZ_1_1 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xcb1_5_4_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_5_4_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Yb1_5_4_7 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_1_5 hfuseZ_6_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Ycb1_5_4_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_5_4_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 1 5 4).1 (realGauge.gaugeSizeL 1 5 4).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_5_4_7 TL1_5_4 YLb1_5_4_7 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc1_5_4_0 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 4) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc1_5_4_0 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) = (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (5 : ZMod 8)).1 (realSize (1 : ZMod 8) (5 : ZMod 8)).2 (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_4 (fuseRow ((1 : ZMod 8) + 5) (4 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc1_5_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc1_5_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcc1_5_4_0 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc1_5_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_5_4_0 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc1_5_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_5_4_0 : ∀ I J g, Xc1_5_4_0 I J g = Xcc1_5_4_0 I J g := by
  decide +kernel

theorem hYtabc1_5_4_0 : ∀ I J g, Yc1_5_4_0 I J g = Ycc1_5_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc1_5_4_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_5_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xc1_5_4_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 hfuseZ_5_4 hfuseZ_1_1 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xcc1_5_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_5_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Yc1_5_4_0 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_6_4 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Ycc1_5_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_5_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 1 5 4).1 (realGauge.gaugeSizeL 1 5 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_5_4_0 TL1_5_4 YLc1_5_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc1_5_4_1 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 4) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc1_5_4_1 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) = (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (5 : ZMod 8)).1 (realSize (1 : ZMod 8) (5 : ZMod 8)).2 (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_4 (fuseRow ((1 : ZMod 8) + 5) (4 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc1_5_4_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc1_5_4_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]]]

noncomputable def Xcc1_5_4_1 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc1_5_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_5_4_1 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc1_5_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_5_4_1 : ∀ I J g, Xc1_5_4_1 I J g = Xcc1_5_4_1 I J g := by
  decide +kernel

theorem hYtabc1_5_4_1 : ∀ I J g, Yc1_5_4_1 I J g = Ycc1_5_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc1_5_4_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_5_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xc1_5_4_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 hfuseZ_5_4 hfuseZ_1_1 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xcc1_5_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_5_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Yc1_5_4_1 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_6_4 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Ycc1_5_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_5_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 1 5 4).1 (realGauge.gaugeSizeL 1 5 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_5_4_1 TL1_5_4 YLc1_5_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc1_5_4_2 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 4) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc1_5_4_2 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) = (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (5 : ZMod 8)).1 (realSize (1 : ZMod 8) (5 : ZMod 8)).2 (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_4 (fuseRow ((1 : ZMod 8) + 5) (4 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc1_5_4_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc1_5_4_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc1_5_4_2 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc1_5_4_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_5_4_2 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc1_5_4_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_5_4_2 : ∀ I J g, Xc1_5_4_2 I J g = Xcc1_5_4_2 I J g := by
  decide +kernel

theorem hYtabc1_5_4_2 : ∀ I J g, Yc1_5_4_2 I J g = Ycc1_5_4_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc1_5_4_2 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_5_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xc1_5_4_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 hfuseZ_5_4 hfuseZ_1_1 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xcc1_5_4_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_5_4_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Yc1_5_4_2 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_6_4 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Ycc1_5_4_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_5_4_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 1 5 4).1 (realGauge.gaugeSizeL 1 5 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_5_4_2 TL1_5_4 YLc1_5_4_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc1_5_4_3 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) (ro (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 4) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 I) (ri (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc1_5_4_3 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) = (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (5 : ZMod 8)).1 (realSize (1 : ZMod 8) (5 : ZMod 8)).2 (lo (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_4 (fuseRow ((1 : ZMod 8) + 5) (4 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc1_5_4_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc1_5_4_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0]],
   [[0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc1_5_4_3 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc1_5_4_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_5_4_3 : (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc1_5_4_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_5_4_3 : ∀ I J g, Xc1_5_4_3 I J g = Xcc1_5_4_3 I J g := by
  decide +kernel

theorem hYtabc1_5_4_3 : ∀ I J g, Yc1_5_4_3 I J g = Ycc1_5_4_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc1_5_4_3 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_5_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xc1_5_4_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 hfuseZ_5_4 hfuseZ_1_1 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Xcc1_5_4_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_5_4_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Yc1_5_4_3 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_6_4 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 4)) Ycc1_5_4_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 4).2)) (realRepBasis ((1 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_5_4_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 1 5 4).1 (realGauge.gaugeSizeL 1 5 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_5_4_3 TL1_5_4 YLc1_5_4_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint1_5_4 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T1_5_4
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_5_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hinta1_5_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hinta1_5_4_1

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint1_5_4 (i : Fin (realRepDim (5 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) i)) * T1_5_4
      = ((sgn (realRepBasisParity (5 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_5_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h0]; exact hintb1_5_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h1]; exact hintb1_5_4_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h2]; exact hintb1_5_4_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h3]; exact hintb1_5_4_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h4]; exact hintb1_5_4_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h5]; exact hintb1_5_4_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h6]; exact hintb1_5_4_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h7]; exact hintb1_5_4_7

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint1_5_4 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T1_5_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_5_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hintc1_5_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hintc1_5_4_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hintc1_5_4_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hintc1_5_4_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT1_5_4_mem_gInterSpace :
    gtOfT ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 T1_5_4 ∈ gInterSpace ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 hT1_5_4 hAint1_5_4 hBint1_5_4 hCint1_5_4

theorem gtOfT1_5_4_ne_zero : gtOfT ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 T1_5_4 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz1_5_4 T1_5_4_ne_zero

theorem gInterSpace1_5_4_ne_bot : gInterSpace ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT1_5_4_mem_gInterSpace, gtOfT1_5_4_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_1_5_4 : gParity ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) gInterSpace1_5_4_ne_bot).symm

end Triple_1_5_4

/-! ### The triple `(1,5,5)`

`gaugeSizeL = gaugeSizeR = (2,2)`, `dim D_3 = 8`, certgen parity `0`; the transported connector literal. -/
section Triple_1_5_5
open Module
theorem hsz1_5_5 : realGauge.gaugeSizeR 1 5 5 = realGauge.gaugeSizeL 1 5 5 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`4 x 4 x 8`). -/
def TL1_5_5 : List (List (List ℤ)) :=
  [[[1, 0, 0, 1, 0, 1, 1, 0], [1, 0, 0, 1, 0, -1, -1, 0], [0, 1, -1, 0, 1, 0, 0, -1], [0, -1, 1, 0, 1, 0, 0, -1]],
   [[1, 0, 0, -1, 0, -1, 1, 0], [1, 0, 0, -1, 0, 1, -1, 0], [0, 1, 1, 0, -1, 0, 0, -1], [0, -1, -1, 0, -1, 0, 0, -1]],
   [[0, -1, -1, 0, -1, 0, 0, -1], [0, -1, -1, 0, 1, 0, 0, 1], [-1, 0, 0, 1, 0, -1, 1, 0], [1, 0, 0, -1, 0, -1, 1, 0]],
   [[0, 1, -1, 0, -1, 0, 0, 1], [0, 1, -1, 0, 1, 0, 0, -1], [1, 0, 0, 1, 0, -1, -1, 0], [-1, 0, 0, -1, 0, -1, -1, 0]]]

/-- The same literal read at the composite frame `Fin 2 ⊕ Fin 2`. -/
noncomputable def Tc1_5_5 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet TL1_5_5 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_3`. -/
noncomputable def T1_5_5 : ((realGauge.D ((1 : ZMod 8) + 5 + 5)).matrixSuper
    (realGauge.gaugeSizeL 1 5 5).1 (realGauge.gaugeSizeL 1 5 5).2).carrier :=
  matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Tc1_5_5

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT1_5_5 : T1_5_5 ∈ ((realGauge.D ((1 : ZMod 8) + 5 + 5)).matrixSuper
    (realGauge.gaugeSizeL 1 5 5).1 (realGauge.gaugeSizeL 1 5 5).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((1 : ZMod 8) + 5 + 5) Tc1_5_5 0 (by decide)

theorem T1_5_5_ne_zero : T1_5_5 ≠ 0 :=
  matOfCoeff_ne_zero ((1 : ZMod 8) + 5 + 5) Tc1_5_5 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa1_5_5_0 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) = (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (5 : ZMod 8)).1 (realSize (5 : ZMod 8) (5 : ZMod 8)).2 (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I)
          * realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 5) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya1_5_5_0 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_5 (fuseRow ((1 : ZMod 8) + 5) (5 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa1_5_5_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa1_5_5_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca1_5_5_0 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa1_5_5_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_5_5_0 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa1_5_5_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_5_5_0 : ∀ I J g, Xa1_5_5_0 I J g = Xca1_5_5_0 I J g := by
  decide +kernel

theorem hYtaba1_5_5_0 : ∀ I J g, Ya1_5_5_0 I J g = Yca1_5_5_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta1_5_5_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_5_5
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xa1_5_5_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xca1_5_5_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_5_5_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Ya1_5_5_0 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hfuseZ_1_5 hfuseZ_6_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Yca1_5_5_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_5_5_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 5) (realGauge.gaugeSizeL 1 5 5).1 (realGauge.gaugeSizeL 1 5 5).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa1_5_5_0 TL1_5_5 YLa1_5_5_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa1_5_5_1 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) = (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (5 : ZMod 8)).1 (realSize (5 : ZMod 8) (5 : ZMod 8)).2 (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I)
          * realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 5) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 5) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya1_5_5_1 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_5 (fuseRow ((1 : ZMod 8) + 5) (5 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa1_5_5_1 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa1_5_5_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca1_5_5_1 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa1_5_5_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_5_5_1 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa1_5_5_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_5_5_1 : ∀ I J g, Xa1_5_5_1 I J g = Xca1_5_5_1 I J g := by
  decide +kernel

theorem hYtaba1_5_5_1 : ∀ I J g, Ya1_5_5_1 I J g = Yca1_5_5_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta1_5_5_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_5_5
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xa1_5_5_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 hfuseZ_1_2 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xca1_5_5_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_5_5_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Ya1_5_5_1 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hfuseZ_1_5 hfuseZ_6_5 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Yca1_5_5_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_5_5_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 5) (realGauge.gaugeSizeL 1 5 5).1 (realGauge.gaugeSizeL 1 5 5).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa1_5_5_1 TL1_5_5 YLa1_5_5_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb1_5_5_0 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 5) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb1_5_5_0 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_5 (fuseRow ((1 : ZMod 8) + 5) (5 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb1_5_5_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb1_5_5_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb1_5_5_0 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb1_5_5_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_5_5_0 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb1_5_5_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_5_5_0 : ∀ I J g, Xb1_5_5_0 I J g = Xcb1_5_5_0 I J g := by
  decide +kernel

theorem hYtabb1_5_5_0 : ∀ I J g, Yb1_5_5_0 I J g = Ycb1_5_5_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb1_5_5_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_5_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xb1_5_5_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 hfuseZ_5_5 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xcb1_5_5_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_5_5_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Yb1_5_5_0 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hfuseZ_1_5 hfuseZ_6_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Ycb1_5_5_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_5_5_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 5) (realGauge.gaugeSizeL 1 5 5).1 (realGauge.gaugeSizeL 1 5 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_5_5_0 TL1_5_5 YLb1_5_5_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb1_5_5_1 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 5) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb1_5_5_1 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_5 (fuseRow ((1 : ZMod 8) + 5) (5 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb1_5_5_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb1_5_5_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0]],
   [[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb1_5_5_1 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb1_5_5_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_5_5_1 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb1_5_5_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_5_5_1 : ∀ I J g, Xb1_5_5_1 I J g = Xcb1_5_5_1 I J g := by
  decide +kernel

theorem hYtabb1_5_5_1 : ∀ I J g, Yb1_5_5_1 I J g = Ycb1_5_5_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb1_5_5_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_5_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xb1_5_5_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 hfuseZ_5_5 hfuseZ_1_2 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xcb1_5_5_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_5_5_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Yb1_5_5_1 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hfuseZ_1_5 hfuseZ_6_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Ycb1_5_5_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_5_5_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 5) (realGauge.gaugeSizeL 1 5 5).1 (realGauge.gaugeSizeL 1 5 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_5_5_1 TL1_5_5 YLb1_5_5_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb1_5_5_2 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 5) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb1_5_5_2 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_5 (fuseRow ((1 : ZMod 8) + 5) (5 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb1_5_5_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb1_5_5_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]]]

noncomputable def Xcb1_5_5_2 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb1_5_5_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_5_5_2 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb1_5_5_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_5_5_2 : ∀ I J g, Xb1_5_5_2 I J g = Xcb1_5_5_2 I J g := by
  decide +kernel

theorem hYtabb1_5_5_2 : ∀ I J g, Yb1_5_5_2 I J g = Ycb1_5_5_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb1_5_5_2 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_5_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xb1_5_5_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 hfuseZ_5_5 hfuseZ_1_2 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xcb1_5_5_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_5_5_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Yb1_5_5_2 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hfuseZ_1_5 hfuseZ_6_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Ycb1_5_5_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_5_5_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 5) (realGauge.gaugeSizeL 1 5 5).1 (realGauge.gaugeSizeL 1 5 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_5_5_2 TL1_5_5 YLb1_5_5_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb1_5_5_3 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 5) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb1_5_5_3 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_5 (fuseRow ((1 : ZMod 8) + 5) (5 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb1_5_5_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb1_5_5_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0]],
   [[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb1_5_5_3 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb1_5_5_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_5_5_3 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb1_5_5_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_5_5_3 : ∀ I J g, Xb1_5_5_3 I J g = Xcb1_5_5_3 I J g := by
  decide +kernel

theorem hYtabb1_5_5_3 : ∀ I J g, Yb1_5_5_3 I J g = Ycb1_5_5_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb1_5_5_3 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_5_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xb1_5_5_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 hfuseZ_5_5 hfuseZ_1_2 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xcb1_5_5_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_5_5_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Yb1_5_5_3 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hfuseZ_1_5 hfuseZ_6_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Ycb1_5_5_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_5_5_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 5) (realGauge.gaugeSizeL 1 5 5).1 (realGauge.gaugeSizeL 1 5 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_5_5_3 TL1_5_5 YLb1_5_5_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Xb1_5_5_4 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 5) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Yb1_5_5_4 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_5 (fuseRow ((1 : ZMod 8) + 5) (5 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `4`, pre-tabulated. -/
def XLb1_5_5_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `4`, pre-tabulated. -/
def YLb1_5_5_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb1_5_5_4 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb1_5_5_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_5_5_4 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb1_5_5_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_5_5_4 : ∀ I J g, Xb1_5_5_4 I J g = Xcb1_5_5_4 I J g := by
  decide +kernel

theorem hYtabb1_5_5_4 : ∀ I J g, Yb1_5_5_4 I J g = Ycb1_5_5_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `4`** (Koszul sign `+1`). -/
theorem hintb1_5_5_4 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_5_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xb1_5_5_4 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 hfuseZ_5_5 hfuseZ_1_2 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xcb1_5_5_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_5_5_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Yb1_5_5_4 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hfuseZ_1_5 hfuseZ_6_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Ycb1_5_5_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_5_5_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 5) (realGauge.gaugeSizeL 1 5 5).1 (realGauge.gaugeSizeL 1 5 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_5_5_4 TL1_5_5 YLb1_5_5_4 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Xb1_5_5_5 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 5) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Yb1_5_5_5 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_5 (fuseRow ((1 : ZMod 8) + 5) (5 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `5`, pre-tabulated. -/
def XLb1_5_5_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0]],
   [[0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `5`, pre-tabulated. -/
def YLb1_5_5_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb1_5_5_5 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb1_5_5_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_5_5_5 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb1_5_5_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_5_5_5 : ∀ I J g, Xb1_5_5_5 I J g = Xcb1_5_5_5 I J g := by
  decide +kernel

theorem hYtabb1_5_5_5 : ∀ I J g, Yb1_5_5_5 I J g = Ycb1_5_5_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintb1_5_5_5 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_5_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xb1_5_5_5 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 hfuseZ_5_5 hfuseZ_1_2 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xcb1_5_5_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_5_5_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Yb1_5_5_5 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hfuseZ_1_5 hfuseZ_6_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Ycb1_5_5_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_5_5_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 5) (realGauge.gaugeSizeL 1 5 5).1 (realGauge.gaugeSizeL 1 5 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_5_5_5 TL1_5_5 YLb1_5_5_5 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Xb1_5_5_6 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 5) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Yb1_5_5_6 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_5 (fuseRow ((1 : ZMod 8) + 5) (5 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `6`, pre-tabulated. -/
def XLb1_5_5_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0]],
   [[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `6`, pre-tabulated. -/
def YLb1_5_5_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb1_5_5_6 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb1_5_5_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_5_5_6 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb1_5_5_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_5_5_6 : ∀ I J g, Xb1_5_5_6 I J g = Xcb1_5_5_6 I J g := by
  decide +kernel

theorem hYtabb1_5_5_6 : ∀ I J g, Yb1_5_5_6 I J g = Ycb1_5_5_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintb1_5_5_6 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_5_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xb1_5_5_6 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 hfuseZ_5_5 hfuseZ_1_2 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xcb1_5_5_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_5_5_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Yb1_5_5_6 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hfuseZ_1_5 hfuseZ_6_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Ycb1_5_5_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_5_5_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 5) (realGauge.gaugeSizeL 1 5 5).1 (realGauge.gaugeSizeL 1 5 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_5_5_6 TL1_5_5 YLb1_5_5_6 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Xb1_5_5_7 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 5) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Yb1_5_5_7 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_5 (fuseRow ((1 : ZMod 8) + 5) (5 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `7`, pre-tabulated. -/
def XLb1_5_5_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `7`, pre-tabulated. -/
def YLb1_5_5_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb1_5_5_7 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb1_5_5_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_5_5_7 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb1_5_5_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_5_5_7 : ∀ I J g, Xb1_5_5_7 I J g = Xcb1_5_5_7 I J g := by
  decide +kernel

theorem hYtabb1_5_5_7 : ∀ I J g, Yb1_5_5_7 I J g = Ycb1_5_5_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `7`** (Koszul sign `+1`). -/
theorem hintb1_5_5_7 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_5_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xb1_5_5_7 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 hfuseZ_5_5 hfuseZ_1_2 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xcb1_5_5_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_5_5_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Yb1_5_5_7 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hfuseZ_1_5 hfuseZ_6_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Ycb1_5_5_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_5_5_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 5) (realGauge.gaugeSizeL 1 5 5).1 (realGauge.gaugeSizeL 1 5 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_5_5_7 TL1_5_5 YLb1_5_5_7 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc1_5_5_0 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 5) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc1_5_5_0 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) = (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (5 : ZMod 8)).1 (realSize (1 : ZMod 8) (5 : ZMod 8)).2 (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_5 (fuseRow ((1 : ZMod 8) + 5) (5 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc1_5_5_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc1_5_5_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcc1_5_5_0 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc1_5_5_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_5_5_0 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc1_5_5_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_5_5_0 : ∀ I J g, Xc1_5_5_0 I J g = Xcc1_5_5_0 I J g := by
  decide +kernel

theorem hYtabc1_5_5_0 : ∀ I J g, Yc1_5_5_0 I J g = Ycc1_5_5_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc1_5_5_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_5_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xc1_5_5_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 hfuseZ_5_5 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xcc1_5_5_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_5_5_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Yc1_5_5_0 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hfuseZ_6_5 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Ycc1_5_5_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_5_5_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 5) (realGauge.gaugeSizeL 1 5 5).1 (realGauge.gaugeSizeL 1 5 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_5_5_0 TL1_5_5 YLc1_5_5_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc1_5_5_1 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 5) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc1_5_5_1 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) = (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (5 : ZMod 8)).1 (realSize (1 : ZMod 8) (5 : ZMod 8)).2 (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_5 (fuseRow ((1 : ZMod 8) + 5) (5 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc1_5_5_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc1_5_5_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcc1_5_5_1 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc1_5_5_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_5_5_1 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc1_5_5_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_5_5_1 : ∀ I J g, Xc1_5_5_1 I J g = Xcc1_5_5_1 I J g := by
  decide +kernel

theorem hYtabc1_5_5_1 : ∀ I J g, Yc1_5_5_1 I J g = Ycc1_5_5_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc1_5_5_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_5_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xc1_5_5_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 hfuseZ_5_5 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xcc1_5_5_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_5_5_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Yc1_5_5_1 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hfuseZ_6_5 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Ycc1_5_5_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_5_5_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 5) (realGauge.gaugeSizeL 1 5 5).1 (realGauge.gaugeSizeL 1 5 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_5_5_1 TL1_5_5 YLc1_5_5_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc1_5_5_2 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 5) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc1_5_5_2 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) = (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (5 : ZMod 8)).1 (realSize (1 : ZMod 8) (5 : ZMod 8)).2 (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_5 (fuseRow ((1 : ZMod 8) + 5) (5 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc1_5_5_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]],
   [[0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc1_5_5_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]],
   [[0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcc1_5_5_2 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc1_5_5_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_5_5_2 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc1_5_5_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_5_5_2 : ∀ I J g, Xc1_5_5_2 I J g = Xcc1_5_5_2 I J g := by
  decide +kernel

theorem hYtabc1_5_5_2 : ∀ I J g, Yc1_5_5_2 I J g = Ycc1_5_5_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc1_5_5_2 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_5_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xc1_5_5_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 hfuseZ_5_5 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xcc1_5_5_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_5_5_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Yc1_5_5_2 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hfuseZ_6_5 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Ycc1_5_5_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_5_5_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 5) (realGauge.gaugeSizeL 1 5 5).1 (realGauge.gaugeSizeL 1 5 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_5_5_2 TL1_5_5 YLc1_5_5_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc1_5_5_3 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 5) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc1_5_5_3 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) = (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (5 : ZMod 8)).1 (realSize (1 : ZMod 8) (5 : ZMod 8)).2 (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_5 (fuseRow ((1 : ZMod 8) + 5) (5 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc1_5_5_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc1_5_5_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0]]]

noncomputable def Xcc1_5_5_3 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc1_5_5_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_5_5_3 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc1_5_5_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_5_5_3 : ∀ I J g, Xc1_5_5_3 I J g = Xcc1_5_5_3 I J g := by
  decide +kernel

theorem hYtabc1_5_5_3 : ∀ I J g, Yc1_5_5_3 I J g = Ycc1_5_5_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc1_5_5_3 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_5_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xc1_5_5_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 hfuseZ_5_5 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xcc1_5_5_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_5_5_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Yc1_5_5_3 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hfuseZ_6_5 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Ycc1_5_5_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_5_5_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 5) (realGauge.gaugeSizeL 1 5 5).1 (realGauge.gaugeSizeL 1 5 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_5_5_3 TL1_5_5 YLc1_5_5_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Xc1_5_5_4 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 5) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Yc1_5_5_4 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) = (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (5 : ZMod 8)).1 (realSize (1 : ZMod 8) (5 : ZMod 8)).2 (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_5 (fuseRow ((1 : ZMod 8) + 5) (5 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `4`, pre-tabulated. -/
def XLc1_5_5_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `4`, pre-tabulated. -/
def YLc1_5_5_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]],
   [[0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcc1_5_5_4 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc1_5_5_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_5_5_4 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc1_5_5_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_5_5_4 : ∀ I J g, Xc1_5_5_4 I J g = Xcc1_5_5_4 I J g := by
  decide +kernel

theorem hYtabc1_5_5_4 : ∀ I J g, Yc1_5_5_4 I J g = Ycc1_5_5_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `4`** (Koszul sign `+1`). -/
theorem hintc1_5_5_4 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_5_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xc1_5_5_4 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 hfuseZ_5_5 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xcc1_5_5_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_5_5_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Yc1_5_5_4 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hfuseZ_6_5 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Ycc1_5_5_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_5_5_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 5) (realGauge.gaugeSizeL 1 5 5).1 (realGauge.gaugeSizeL 1 5 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_5_5_4 TL1_5_5 YLc1_5_5_4 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Xc1_5_5_5 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 5) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Yc1_5_5_5 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) = (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (5 : ZMod 8)).1 (realSize (1 : ZMod 8) (5 : ZMod 8)).2 (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_5 (fuseRow ((1 : ZMod 8) + 5) (5 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `5`, pre-tabulated. -/
def XLc1_5_5_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `5`, pre-tabulated. -/
def YLc1_5_5_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, -1, 0]]]

noncomputable def Xcc1_5_5_5 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc1_5_5_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_5_5_5 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc1_5_5_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_5_5_5 : ∀ I J g, Xc1_5_5_5 I J g = Xcc1_5_5_5 I J g := by
  decide +kernel

theorem hYtabc1_5_5_5 : ∀ I J g, Yc1_5_5_5 I J g = Ycc1_5_5_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintc1_5_5_5 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_5_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xc1_5_5_5 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 hfuseZ_5_5 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xcc1_5_5_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_5_5_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Yc1_5_5_5 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hfuseZ_6_5 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Ycc1_5_5_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_5_5_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 5) (realGauge.gaugeSizeL 1 5 5).1 (realGauge.gaugeSizeL 1 5 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_5_5_5 TL1_5_5 YLc1_5_5_5 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Xc1_5_5_6 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 5) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Yc1_5_5_6 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) = (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (5 : ZMod 8)).1 (realSize (1 : ZMod 8) (5 : ZMod 8)).2 (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_5 (fuseRow ((1 : ZMod 8) + 5) (5 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `6`, pre-tabulated. -/
def XLc1_5_5_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]]]

/-- Left route at the `c`-slot generator `6`, pre-tabulated. -/
def YLc1_5_5_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0]]]

noncomputable def Xcc1_5_5_6 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc1_5_5_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_5_5_6 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc1_5_5_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_5_5_6 : ∀ I J g, Xc1_5_5_6 I J g = Xcc1_5_5_6 I J g := by
  decide +kernel

theorem hYtabc1_5_5_6 : ∀ I J g, Yc1_5_5_6 I J g = Ycc1_5_5_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintc1_5_5_6 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_5_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xc1_5_5_6 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 hfuseZ_5_5 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xcc1_5_5_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_5_5_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Yc1_5_5_6 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hfuseZ_6_5 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Ycc1_5_5_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_5_5_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 5) (realGauge.gaugeSizeL 1 5 5).1 (realGauge.gaugeSizeL 1 5 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_5_5_6 TL1_5_5 YLc1_5_5_6 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Xc1_5_5_7 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ro (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((5 : ZMod 8) + 5) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 I) (ri (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 J) g) (fuseCol (1 : ZMod 8) ((5 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Yc1_5_5_7 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) = (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (5 : ZMod 8)).1 (realSize (1 : ZMod 8) (5 : ZMod 8)).2 (lo (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_5 (fuseRow ((1 : ZMod 8) + 5) (5 : ZMod 8) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 5) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `7`, pre-tabulated. -/
def XLc1_5_5_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `7`, pre-tabulated. -/
def YLc1_5_5_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0]],
   [[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcc1_5_5_7 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc1_5_5_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_5_5_7 : (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2) → Fin (realRepDim ((1 : ZMod 8) + 5 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc1_5_5_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_5_5_7 : ∀ I J g, Xc1_5_5_7 I J g = Xcc1_5_5_7 I J g := by
  decide +kernel

theorem hYtabc1_5_5_7 : ∀ I J g, Yc1_5_5_7 I J g = Ycc1_5_5_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `7`** (Koszul sign `+1`). -/
theorem hintc1_5_5_7 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_5_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_5_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xc1_5_5_7 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 hfuseZ_5_5 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Xcc1_5_5_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_5_5_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Yc1_5_5_7 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hfuseZ_6_5 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 5 + 5)) Ycc1_5_5_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 5 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 5 5).2)) (realRepBasis ((1 : ZMod 8) + 5 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_5_5_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 5 + 5) (realGauge.gaugeSizeL 1 5 5).1 (realGauge.gaugeSizeL 1 5 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_5_5_7 TL1_5_5 YLc1_5_5_7 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint1_5_5 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T1_5_5
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_5_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hinta1_5_5_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hinta1_5_5_1

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint1_5_5 (i : Fin (realRepDim (5 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) i)) * T1_5_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_5_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h0]; exact hintb1_5_5_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h1]; exact hintb1_5_5_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h2]; exact hintb1_5_5_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h3]; exact hintb1_5_5_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h4]; exact hintb1_5_5_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h5]; exact hintb1_5_5_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h6]; exact hintb1_5_5_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h7]; exact hintb1_5_5_7

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint1_5_5 (i : Fin (realRepDim (5 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) i)) * T1_5_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_5_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h0]; exact hintc1_5_5_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h1]; exact hintc1_5_5_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h2]; exact hintc1_5_5_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h3]; exact hintc1_5_5_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h4]; exact hintc1_5_5_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h5]; exact hintc1_5_5_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h6]; exact hintc1_5_5_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h7]; exact hintc1_5_5_7

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT1_5_5_mem_gInterSpace :
    gtOfT ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 T1_5_5 ∈ gInterSpace ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 hT1_5_5 hAint1_5_5 hBint1_5_5 hCint1_5_5

theorem gtOfT1_5_5_ne_zero : gtOfT ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 T1_5_5 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) hsz1_5_5 T1_5_5_ne_zero

theorem gInterSpace1_5_5_ne_bot : gInterSpace ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT1_5_5_mem_gInterSpace, gtOfT1_5_5_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_1_5_5 : gParity ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (1 : ZMod 8) (5 : ZMod 8) (5 : ZMod 8) gInterSpace1_5_5_ne_bot).symm

end Triple_1_5_5

end BatchMedium
end TripleCerts
end GaugeChi
end Superfusion

/-! ### Kernel self-check -/

#print axioms Superfusion.GaugeChi.TripleCerts.BatchMedium.gParity_1_1_5
#print axioms Superfusion.GaugeChi.TripleCerts.BatchMedium.gParity_1_1_6
#print axioms Superfusion.GaugeChi.TripleCerts.BatchMedium.gParity_1_2_3
#print axioms Superfusion.GaugeChi.TripleCerts.BatchMedium.gParity_1_2_4
#print axioms Superfusion.GaugeChi.TripleCerts.BatchMedium.gParity_1_3_6
#print axioms Superfusion.GaugeChi.TripleCerts.BatchMedium.gParity_1_4_2
#print axioms Superfusion.GaugeChi.TripleCerts.BatchMedium.gParity_1_5_4
#print axioms Superfusion.GaugeChi.TripleCerts.BatchMedium.gParity_1_5_5
