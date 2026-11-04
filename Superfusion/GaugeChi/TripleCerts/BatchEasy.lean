/-
Superfusion / GaugeChi / TripleCerts / BatchEasy

**GENERATED FILE — do not edit.**  Regenerate with

    python3 scripts/certgen/gen_triple_certs.py \
        --triples 0,0,0 0,0,1 0,0,2 0,0,3 0,0,4 0,0,5 0,0,6 0,0,7 \
        --module BatchEasy \
        --out Superfusion/GaugeChi/TripleCerts/BatchEasy.lean

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

Triples (8): (0,0,0), (0,0,1), (0,0,2), (0,0,3), (0,0,4), (0,0,5), (0,0,6), (0,0,7).
Unit-slot triples (`a = 0` or `b = 0` or `c = 0`) in this batch: (0,0,0), (0,0,1), (0,0,2), (0,0,3), (0,0,4), (0,0,5), (0,0,6), (0,0,7).
All of them have the IDENTITY connector in the transported frame
(measured over all 169), parity `0`, and both permutations trivial —
so their certificates carry the sign `+1` and need no matrix literal
beyond the identity array.  (Their composite frames are NOT all `1|0`.)

No `sorry`, no `native_decide`, no new axioms.
-/
import Superfusion.GaugeChi.RouteBridgeProto
import Superfusion.Gauge.RealFuseSpecPilot

namespace Superfusion
namespace GaugeChi
namespace TripleCerts
namespace BatchEasy

open Module

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

/-! ### The triple `(0,0,0)`

`gaugeSizeL = gaugeSizeR = (1,0)`, `dim D_0 = 1`, certgen parity `0`; the unit-slot shortcut: the connector is the identity, so every certificate carries the sign `+1`. -/
section Triple_0_0_0
open Module
theorem hsz0_0_0 : realGauge.gaugeSizeR 0 0 0 = realGauge.gaugeSizeL 0 0 0 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`1 x 1 x 1`). -/
def TL0_0_0 : List (List (List ℤ)) :=
  [[[1]]]

/-- The same literal read at the composite frame `Fin 1 ⊕ Fin 0`. -/
noncomputable def Tc0_0_0 : (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2) → (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 0).val) → ℤ :=
  fun r s g => coeffGet TL0_0_0 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_0`. -/
noncomputable def T0_0_0 : ((realGauge.D ((0 : ZMod 8) + 0 + 0)).matrixSuper
    (realGauge.gaugeSizeL 0 0 0).1 (realGauge.gaugeSizeL 0 0 0).2).carrier :=
  matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 0)) Tc0_0_0

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT0_0_0 : T0_0_0 ∈ ((realGauge.D ((0 : ZMod 8) + 0 + 0)).matrixSuper
    (realGauge.gaugeSizeL 0 0 0).1 (realGauge.gaugeSizeL 0 0 0).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((0 : ZMod 8) + 0 + 0) Tc0_0_0 0 (by decide)

theorem T0_0_0_ne_zero : T0_0_0 ≠ 0 :=
  matOfCoeff_ne_zero ((0 : ZMod 8) + 0 + 0) Tc0_0_0 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa0_0_0_0 : (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2) → (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 0).val) → ℤ :=
  fun I J g => if (ro (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) hsz0_0_0 I) = (ro (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) hsz0_0_0 J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (ro (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) hsz0_0_0 I)
          * realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_0 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 0) (ri (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) hsz0_0_0 I) (ri (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) hsz0_0_0 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya0_0_0_0 : (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2) → (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_0 (fuseRow (0 : ZMod 8) (0 : ZMod 8) (lo (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) I) (lo (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (0 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_0_0 (fuseRow ((0 : ZMod 8) + 0) (0 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa0_0_0_0 : List (List (List ℤ)) :=
  [[[1]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa0_0_0_0 : List (List (List ℤ)) :=
  [[[1]]]

noncomputable def Xca0_0_0_0 : (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2) → (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa0_0_0_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca0_0_0_0 : (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2) → (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa0_0_0_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 1 = 1` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba0_0_0_0 : ∀ I J g, Xa0_0_0_0 I J g = Xca0_0_0_0 I J g := by
  decide +kernel

theorem hYtaba0_0_0_0 : ∀ I J g, Ya0_0_0_0 I J g = Yca0_0_0_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta0_0_0_0 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))) * T0_0_0
      = ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_0 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 0)) Xa0_0_0_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) hsz0_0_0 hfuseZ_0_0 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 0)) Xca0_0_0_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2)) (realRepBasis ((0 : ZMod 8) + 0 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba0_0_0_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 0)) Ya0_0_0_0 := Matrix.ext fun I J => routeL_aSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) hfuseZ_0_0 hfuseZ_0_0 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 0)) Yca0_0_0_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2)) (realRepBasis ((0 : ZMod 8) + 0 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba0_0_0_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 0) (realGauge.gaugeSizeL 0 0 0).1 (realGauge.gaugeSizeL 0 0 0).2 ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa0_0_0_0 TL0_0_0 YLa0_0_0_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb0_0_0_0 : (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2) → (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_0 (fuseRow (0 : ZMod 8) (0 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) hsz0_0_0 I) (ro (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) hsz0_0_0 J) ee) (fuseCol (0 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_0_0 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 0) (ri (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) hsz0_0_0 I) (ri (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) hsz0_0_0 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb0_0_0_0 : (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2) → (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_0 (fuseRow (0 : ZMod 8) (0 : ZMod 8) (lo (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) I) (lo (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (0 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_0_0 (fuseRow ((0 : ZMod 8) + 0) (0 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb0_0_0_0 : List (List (List ℤ)) :=
  [[[1]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb0_0_0_0 : List (List (List ℤ)) :=
  [[[1]]]

noncomputable def Xcb0_0_0_0 : (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2) → (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb0_0_0_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb0_0_0_0 : (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2) → (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb0_0_0_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 1 = 1` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb0_0_0_0 : ∀ I J g, Xb0_0_0_0 I J g = Xcb0_0_0_0 I J g := by
  decide +kernel

theorem hYtabb0_0_0_0 : ∀ I J g, Yb0_0_0_0 I J g = Ycb0_0_0_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb0_0_0_0 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))) * T0_0_0
      = ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_0 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 0)) Xb0_0_0_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) hsz0_0_0 hfuseZ_0_0 hfuseZ_0_0 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 0)) Xcb0_0_0_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2)) (realRepBasis ((0 : ZMod 8) + 0 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb0_0_0_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 0)) Yb0_0_0_0 := Matrix.ext fun I J => routeL_bSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) hfuseZ_0_0 hfuseZ_0_0 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 0)) Ycb0_0_0_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2)) (realRepBasis ((0 : ZMod 8) + 0 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb0_0_0_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 0) (realGauge.gaugeSizeL 0 0 0).1 (realGauge.gaugeSizeL 0 0 0).2 ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb0_0_0_0 TL0_0_0 YLb0_0_0_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc0_0_0_0 : (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2) → (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_0 (fuseRow (0 : ZMod 8) (0 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) hsz0_0_0 I) (ro (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) hsz0_0_0 J) ee) (fuseCol (0 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_0_0 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 0) (ri (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) hsz0_0_0 I) (ri (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) hsz0_0_0 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc0_0_0_0 : (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2) → (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 0).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) I)
          * realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_0 (fuseRow ((0 : ZMod 8) + 0) (0 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc0_0_0_0 : List (List (List ℤ)) :=
  [[[1]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc0_0_0_0 : List (List (List ℤ)) :=
  [[[1]]]

noncomputable def Xcc0_0_0_0 : (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2) → (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 0).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_0_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_0_0 : (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2) → (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 0).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_0_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 1 = 1` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_0_0 : ∀ I J g, Xc0_0_0_0 I J g = Xcc0_0_0_0 I J g := by
  decide +kernel

theorem hYtabc0_0_0_0 : ∀ I J g, Yc0_0_0_0 I J g = Ycc0_0_0_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc0_0_0_0 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))) * T0_0_0
      = ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_0 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 0)) Xc0_0_0_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) hsz0_0_0 hfuseZ_0_0 hfuseZ_0_0 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 0)) Xcc0_0_0_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2)) (realRepBasis ((0 : ZMod 8) + 0 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_0_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 0)) Yc0_0_0_0 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) hfuseZ_0_0 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 0)) Ycc0_0_0_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 0).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 0).2)) (realRepBasis ((0 : ZMod 8) + 0 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_0_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 0) (realGauge.gaugeSizeL 0 0 0).1 (realGauge.gaugeSizeL 0 0 0).2 ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_0_0 TL0_0_0 YLc0_0_0_0 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint0_0_0 (i : Fin (realRepDim (0 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) i)) * T0_0_0
      = ((sgn (realRepBasisParity (0 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T0_0_0 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 1 := i.isLt
  have h0 : (i : ℕ) = 0 := by omega
  rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) from Fin.ext h0]
  exact hinta0_0_0_0

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint0_0_0 (i : Fin (realRepDim (0 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) i)) * T0_0_0
      = ((sgn (realRepBasisParity (0 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T0_0_0 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 1 := i.isLt
  have h0 : (i : ℕ) = 0 := by omega
  rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) from Fin.ext h0]
  exact hintb0_0_0_0

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint0_0_0 (i : Fin (realRepDim (0 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) i)) * T0_0_0
      = ((sgn (realRepBasisParity (0 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T0_0_0 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 1 := i.isLt
  have h0 : (i : ℕ) = 0 := by omega
  rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) from Fin.ext h0]
  exact hintc0_0_0_0

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT0_0_0_mem_gInterSpace :
    gtOfT ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) hsz0_0_0 T0_0_0 ∈ gInterSpace ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) hsz0_0_0 hT0_0_0 hAint0_0_0 hBint0_0_0 hCint0_0_0

theorem gtOfT0_0_0_ne_zero : gtOfT ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) hsz0_0_0 T0_0_0 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) hsz0_0_0 T0_0_0_ne_zero

theorem gInterSpace0_0_0_ne_bot : gInterSpace ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT0_0_0_mem_gInterSpace, gtOfT0_0_0_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_0_0_0 : gParity ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (0 : ZMod 8) gInterSpace0_0_0_ne_bot).symm

end Triple_0_0_0

/-! ### The triple `(0,0,1)`

`gaugeSizeL = gaugeSizeR = (1,0)`, `dim D_1 = 2`, certgen parity `0`; the unit-slot shortcut: the connector is the identity, so every certificate carries the sign `+1`. -/
section Triple_0_0_1
open Module
theorem hsz0_0_1 : realGauge.gaugeSizeR 0 0 1 = realGauge.gaugeSizeL 0 0 1 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`1 x 1 x 2`). -/
def TL0_0_1 : List (List (List ℤ)) :=
  [[[1, 0]]]

/-- The same literal read at the composite frame `Fin 1 ⊕ Fin 0`. -/
noncomputable def Tc0_0_1 : (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 1).val) → ℤ :=
  fun r s g => coeffGet TL0_0_1 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_1`. -/
noncomputable def T0_0_1 : ((realGauge.D ((0 : ZMod 8) + 0 + 1)).matrixSuper
    (realGauge.gaugeSizeL 0 0 1).1 (realGauge.gaugeSizeL 0 0 1).2).carrier :=
  matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 1)) Tc0_0_1

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT0_0_1 : T0_0_1 ∈ ((realGauge.D ((0 : ZMod 8) + 0 + 1)).matrixSuper
    (realGauge.gaugeSizeL 0 0 1).1 (realGauge.gaugeSizeL 0 0 1).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((0 : ZMod 8) + 0 + 1) Tc0_0_1 0 (by decide)

theorem T0_0_1_ne_zero : T0_0_1 ≠ 0 :=
  matOfCoeff_ne_zero ((0 : ZMod 8) + 0 + 1) Tc0_0_1 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa0_0_1_0 : (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 1).val) → ℤ :=
  fun I J g => if (ro (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hsz0_0_1 I) = (ro (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hsz0_0_1 J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (1 : ZMod 8)).1 (realSize (0 : ZMod 8) (1 : ZMod 8)).2 (ro (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hsz0_0_1 I)
          * realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_1 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 1) (ri (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hsz0_0_1 I) (ri (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hsz0_0_1 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya0_0_1_0 : (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_0 (fuseRow (0 : ZMod 8) (0 : ZMod 8) (lo (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) I) (lo (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (0 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_0_1 (fuseRow ((0 : ZMod 8) + 0) (1 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa0_0_1_0 : List (List (List ℤ)) :=
  [[[1, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa0_0_1_0 : List (List (List ℤ)) :=
  [[[1, 0]]]

noncomputable def Xca0_0_1_0 : (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 1).val) → ℤ :=
  fun r s g => coeffGet XLa0_0_1_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca0_0_1_0 : (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 1).val) → ℤ :=
  fun r s g => coeffGet YLa0_0_1_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 2 = 2` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba0_0_1_0 : ∀ I J g, Xa0_0_1_0 I J g = Xca0_0_1_0 I J g := by
  decide +kernel

theorem hYtaba0_0_1_0 : ∀ I J g, Ya0_0_1_0 I J g = Yca0_0_1_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta0_0_1_0 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))) * T0_0_1
      = ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_1 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 1)) Xa0_0_1_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hsz0_0_1 hfuseZ_0_1 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 1)) Xca0_0_1_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2)) (realRepBasis ((0 : ZMod 8) + 0 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtaba0_0_1_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 1)) Ya0_0_1_0 := Matrix.ext fun I J => routeL_aSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hfuseZ_0_0 hfuseZ_0_1 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 1)) Yca0_0_1_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2)) (realRepBasis ((0 : ZMod 8) + 0 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtaba0_0_1_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 1) (realGauge.gaugeSizeL 0 0 1).1 (realGauge.gaugeSizeL 0 0 1).2 ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa0_0_1_0 TL0_0_1 YLa0_0_1_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb0_0_1_0 : (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_1 (fuseRow (0 : ZMod 8) (1 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hsz0_0_1 I) (ro (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hsz0_0_1 J) ee) (fuseCol (0 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_0_1 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 1) (ri (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hsz0_0_1 I) (ri (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hsz0_0_1 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb0_0_1_0 : (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_0 (fuseRow (0 : ZMod 8) (0 : ZMod 8) (lo (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) I) (lo (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (0 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_0_1 (fuseRow ((0 : ZMod 8) + 0) (1 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb0_0_1_0 : List (List (List ℤ)) :=
  [[[1, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb0_0_1_0 : List (List (List ℤ)) :=
  [[[1, 0]]]

noncomputable def Xcb0_0_1_0 : (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 1).val) → ℤ :=
  fun r s g => coeffGet XLb0_0_1_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb0_0_1_0 : (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 1).val) → ℤ :=
  fun r s g => coeffGet YLb0_0_1_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 2 = 2` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb0_0_1_0 : ∀ I J g, Xb0_0_1_0 I J g = Xcb0_0_1_0 I J g := by
  decide +kernel

theorem hYtabb0_0_1_0 : ∀ I J g, Yb0_0_1_0 I J g = Ycb0_0_1_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb0_0_1_0 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))) * T0_0_1
      = ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_1 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 1)) Xb0_0_1_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hsz0_0_1 hfuseZ_0_1 hfuseZ_0_1 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 1)) Xcb0_0_1_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2)) (realRepBasis ((0 : ZMod 8) + 0 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabb0_0_1_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 1)) Yb0_0_1_0 := Matrix.ext fun I J => routeL_bSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hfuseZ_0_0 hfuseZ_0_1 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 1)) Ycb0_0_1_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2)) (realRepBasis ((0 : ZMod 8) + 0 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabb0_0_1_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 1) (realGauge.gaugeSizeL 0 0 1).1 (realGauge.gaugeSizeL 0 0 1).2 ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb0_0_1_0 TL0_0_1 YLb0_0_1_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc0_0_1_0 : (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_1 (fuseRow (0 : ZMod 8) (1 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hsz0_0_1 I) (ro (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hsz0_0_1 J) ee) (fuseCol (0 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_0_1 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 1) (ri (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hsz0_0_1 I) (ri (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hsz0_0_1 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc0_0_1_0 : (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 1).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) I)
          * realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_1 (fuseRow ((0 : ZMod 8) + 0) (1 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc0_0_1_0 : List (List (List ℤ)) :=
  [[[1, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc0_0_1_0 : List (List (List ℤ)) :=
  [[[1, 0]]]

noncomputable def Xcc0_0_1_0 : (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 1).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_1_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_1_0 : (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 1).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_1_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 2 = 2` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_1_0 : ∀ I J g, Xc0_0_1_0 I J g = Xcc0_0_1_0 I J g := by
  decide +kernel

theorem hYtabc0_0_1_0 : ∀ I J g, Yc0_0_1_0 I J g = Ycc0_0_1_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc0_0_1_0 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T0_0_1
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_1 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 1)) Xc0_0_1_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hsz0_0_1 hfuseZ_0_1 hfuseZ_0_1 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 1)) Xcc0_0_1_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2)) (realRepBasis ((0 : ZMod 8) + 0 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_1_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 1)) Yc0_0_1_0 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hfuseZ_0_1 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 1)) Ycc0_0_1_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2)) (realRepBasis ((0 : ZMod 8) + 0 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_1_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 1) (realGauge.gaugeSizeL 0 0 1).1 (realGauge.gaugeSizeL 0 0 1).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_1_0 TL0_0_1 YLc0_0_1_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc0_0_1_1 : (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_1 (fuseRow (0 : ZMod 8) (1 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hsz0_0_1 I) (ro (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hsz0_0_1 J) ee) (fuseCol (0 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_0_1 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 1) (ri (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hsz0_0_1 I) (ri (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hsz0_0_1 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc0_0_1_1 : (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 1).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) I)
          * realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_1 (fuseRow ((0 : ZMod 8) + 0) (1 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc0_0_1_1 : List (List (List ℤ)) :=
  [[[0, 1]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc0_0_1_1 : List (List (List ℤ)) :=
  [[[0, 1]]]

noncomputable def Xcc0_0_1_1 : (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 1).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_1_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_1_1 : (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 1).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_1_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 2 = 2` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_1_1 : ∀ I J g, Xc0_0_1_1 I J g = Xcc0_0_1_1 I J g := by
  decide +kernel

theorem hYtabc0_0_1_1 : ∀ I J g, Yc0_0_1_1 I J g = Ycc0_0_1_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc0_0_1_1 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T0_0_1
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_1 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 1)) Xc0_0_1_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hsz0_0_1 hfuseZ_0_1 hfuseZ_0_1 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 1)) Xcc0_0_1_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2)) (realRepBasis ((0 : ZMod 8) + 0 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_1_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 1)) Yc0_0_1_1 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hfuseZ_0_1 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 1)) Ycc0_0_1_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 1).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 1).2)) (realRepBasis ((0 : ZMod 8) + 0 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_1_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 1) (realGauge.gaugeSizeL 0 0 1).1 (realGauge.gaugeSizeL 0 0 1).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_1_1 TL0_0_1 YLc0_0_1_1 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint0_0_1 (i : Fin (realRepDim (0 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (0 : ZMod 8) i)) * T0_0_1
      = ((sgn (realRepBasisParity (0 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T0_0_1 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (0 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 1 := i.isLt
  have h0 : (i : ℕ) = 0 := by omega
  rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) from Fin.ext h0]
  exact hinta0_0_1_0

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint0_0_1 (i : Fin (realRepDim (0 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (0 : ZMod 8) i)) * T0_0_1
      = ((sgn (realRepBasisParity (0 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T0_0_1 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (0 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 1 := i.isLt
  have h0 : (i : ℕ) = 0 := by omega
  rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) from Fin.ext h0]
  exact hintb0_0_1_0

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint0_0_1 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T0_0_1
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T0_0_1 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hintc0_0_1_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hintc0_0_1_1

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT0_0_1_mem_gInterSpace :
    gtOfT ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hsz0_0_1 T0_0_1 ∈ gInterSpace ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hsz0_0_1 hT0_0_1 hAint0_0_1 hBint0_0_1 hCint0_0_1

theorem gtOfT0_0_1_ne_zero : gtOfT ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hsz0_0_1 T0_0_1 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) hsz0_0_1 T0_0_1_ne_zero

theorem gInterSpace0_0_1_ne_bot : gInterSpace ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT0_0_1_mem_gInterSpace, gtOfT0_0_1_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_0_0_1 : gParity ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (1 : ZMod 8) gInterSpace0_0_1_ne_bot).symm

end Triple_0_0_1

/-! ### The triple `(0,0,2)`

`gaugeSizeL = gaugeSizeR = (1,0)`, `dim D_2 = 4`, certgen parity `0`; the unit-slot shortcut: the connector is the identity, so every certificate carries the sign `+1`. -/
section Triple_0_0_2
open Module
theorem hsz0_0_2 : realGauge.gaugeSizeR 0 0 2 = realGauge.gaugeSizeL 0 0 2 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`1 x 1 x 4`). -/
def TL0_0_2 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0]]]

/-- The same literal read at the composite frame `Fin 1 ⊕ Fin 0`. -/
noncomputable def Tc0_0_2 : (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 2).val) → ℤ :=
  fun r s g => coeffGet TL0_0_2 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_2`. -/
noncomputable def T0_0_2 : ((realGauge.D ((0 : ZMod 8) + 0 + 2)).matrixSuper
    (realGauge.gaugeSizeL 0 0 2).1 (realGauge.gaugeSizeL 0 0 2).2).carrier :=
  matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 2)) Tc0_0_2

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT0_0_2 : T0_0_2 ∈ ((realGauge.D ((0 : ZMod 8) + 0 + 2)).matrixSuper
    (realGauge.gaugeSizeL 0 0 2).1 (realGauge.gaugeSizeL 0 0 2).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((0 : ZMod 8) + 0 + 2) Tc0_0_2 0 (by decide)

theorem T0_0_2_ne_zero : T0_0_2 ≠ 0 :=
  matOfCoeff_ne_zero ((0 : ZMod 8) + 0 + 2) Tc0_0_2 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa0_0_2_0 : (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 2).val) → ℤ :=
  fun I J g => if (ro (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 I) = (ro (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (2 : ZMod 8)).1 (realSize (0 : ZMod 8) (2 : ZMod 8)).2 (ro (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 I)
          * realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_2 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 2) (ri (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 I) (ri (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya0_0_2_0 : (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_0 (fuseRow (0 : ZMod 8) (0 : ZMod 8) (lo (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) I) (lo (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (0 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_0_2 (fuseRow ((0 : ZMod 8) + 0) (2 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa0_0_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa0_0_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0]]]

noncomputable def Xca0_0_2_0 : (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa0_0_2_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca0_0_2_0 : (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa0_0_2_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 4 = 4` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba0_0_2_0 : ∀ I J g, Xa0_0_2_0 I J g = Xca0_0_2_0 I J g := by
  decide +kernel

theorem hYtaba0_0_2_0 : ∀ I J g, Ya0_0_2_0 I J g = Yca0_0_2_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta0_0_2_0 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))) * T0_0_2
      = ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_2 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 2)) Xa0_0_2_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 hfuseZ_0_2 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 2)) Xca0_0_2_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2)) (realRepBasis ((0 : ZMod 8) + 0 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba0_0_2_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 2)) Ya0_0_2_0 := Matrix.ext fun I J => routeL_aSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hfuseZ_0_0 hfuseZ_0_2 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 2)) Yca0_0_2_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2)) (realRepBasis ((0 : ZMod 8) + 0 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba0_0_2_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 2) (realGauge.gaugeSizeL 0 0 2).1 (realGauge.gaugeSizeL 0 0 2).2 ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa0_0_2_0 TL0_0_2 YLa0_0_2_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb0_0_2_0 : (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_2 (fuseRow (0 : ZMod 8) (2 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 I) (ro (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 J) ee) (fuseCol (0 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_0_2 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 2) (ri (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 I) (ri (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb0_0_2_0 : (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_0 (fuseRow (0 : ZMod 8) (0 : ZMod 8) (lo (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) I) (lo (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (0 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_0_2 (fuseRow ((0 : ZMod 8) + 0) (2 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb0_0_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb0_0_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0]]]

noncomputable def Xcb0_0_2_0 : (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb0_0_2_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb0_0_2_0 : (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb0_0_2_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 4 = 4` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb0_0_2_0 : ∀ I J g, Xb0_0_2_0 I J g = Xcb0_0_2_0 I J g := by
  decide +kernel

theorem hYtabb0_0_2_0 : ∀ I J g, Yb0_0_2_0 I J g = Ycb0_0_2_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb0_0_2_0 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))) * T0_0_2
      = ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_2 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 2)) Xb0_0_2_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 hfuseZ_0_2 hfuseZ_0_2 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 2)) Xcb0_0_2_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2)) (realRepBasis ((0 : ZMod 8) + 0 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb0_0_2_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 2)) Yb0_0_2_0 := Matrix.ext fun I J => routeL_bSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hfuseZ_0_0 hfuseZ_0_2 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 2)) Ycb0_0_2_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2)) (realRepBasis ((0 : ZMod 8) + 0 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb0_0_2_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 2) (realGauge.gaugeSizeL 0 0 2).1 (realGauge.gaugeSizeL 0 0 2).2 ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb0_0_2_0 TL0_0_2 YLb0_0_2_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc0_0_2_0 : (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_2 (fuseRow (0 : ZMod 8) (2 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 I) (ro (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 J) ee) (fuseCol (0 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_0_2 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 2) (ri (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 I) (ri (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc0_0_2_0 : (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 2).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_2 (fuseRow ((0 : ZMod 8) + 0) (2 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc0_0_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc0_0_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0]]]

noncomputable def Xcc0_0_2_0 : (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_2_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_2_0 : (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_2_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 4 = 4` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_2_0 : ∀ I J g, Xc0_0_2_0 I J g = Xcc0_0_2_0 I J g := by
  decide +kernel

theorem hYtabc0_0_2_0 : ∀ I J g, Yc0_0_2_0 I J g = Ycc0_0_2_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc0_0_2_0 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T0_0_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_2 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 2)) Xc0_0_2_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 hfuseZ_0_2 hfuseZ_0_2 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 2)) Xcc0_0_2_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2)) (realRepBasis ((0 : ZMod 8) + 0 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_2_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 2)) Yc0_0_2_0 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hfuseZ_0_2 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 2)) Ycc0_0_2_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2)) (realRepBasis ((0 : ZMod 8) + 0 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_2_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 2) (realGauge.gaugeSizeL 0 0 2).1 (realGauge.gaugeSizeL 0 0 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_2_0 TL0_0_2 YLc0_0_2_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc0_0_2_1 : (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_2 (fuseRow (0 : ZMod 8) (2 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 I) (ro (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 J) ee) (fuseCol (0 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_0_2 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 2) (ri (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 I) (ri (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc0_0_2_1 : (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 2).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_2 (fuseRow ((0 : ZMod 8) + 0) (2 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc0_0_2_1 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc0_0_2_1 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0]]]

noncomputable def Xcc0_0_2_1 : (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_2_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_2_1 : (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_2_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 4 = 4` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_2_1 : ∀ I J g, Xc0_0_2_1 I J g = Xcc0_0_2_1 I J g := by
  decide +kernel

theorem hYtabc0_0_2_1 : ∀ I J g, Yc0_0_2_1 I J g = Ycc0_0_2_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc0_0_2_1 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T0_0_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_2 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 2)) Xc0_0_2_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 hfuseZ_0_2 hfuseZ_0_2 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 2)) Xcc0_0_2_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2)) (realRepBasis ((0 : ZMod 8) + 0 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_2_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 2)) Yc0_0_2_1 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hfuseZ_0_2 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 2)) Ycc0_0_2_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2)) (realRepBasis ((0 : ZMod 8) + 0 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_2_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 2) (realGauge.gaugeSizeL 0 0 2).1 (realGauge.gaugeSizeL 0 0 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_2_1 TL0_0_2 YLc0_0_2_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc0_0_2_2 : (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_2 (fuseRow (0 : ZMod 8) (2 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 I) (ro (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 J) ee) (fuseCol (0 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_0_2 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 2) (ri (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 I) (ri (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc0_0_2_2 : (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 2).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_2 (fuseRow ((0 : ZMod 8) + 0) (2 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc0_0_2_2 : List (List (List ℤ)) :=
  [[[0, 0, 1, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc0_0_2_2 : List (List (List ℤ)) :=
  [[[0, 0, 1, 0]]]

noncomputable def Xcc0_0_2_2 : (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_2_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_2_2 : (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_2_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 4 = 4` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_2_2 : ∀ I J g, Xc0_0_2_2 I J g = Xcc0_0_2_2 I J g := by
  decide +kernel

theorem hYtabc0_0_2_2 : ∀ I J g, Yc0_0_2_2 I J g = Ycc0_0_2_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc0_0_2_2 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T0_0_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_2 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 2)) Xc0_0_2_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 hfuseZ_0_2 hfuseZ_0_2 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 2)) Xcc0_0_2_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2)) (realRepBasis ((0 : ZMod 8) + 0 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_2_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 2)) Yc0_0_2_2 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hfuseZ_0_2 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 2)) Ycc0_0_2_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2)) (realRepBasis ((0 : ZMod 8) + 0 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_2_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 2) (realGauge.gaugeSizeL 0 0 2).1 (realGauge.gaugeSizeL 0 0 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_2_2 TL0_0_2 YLc0_0_2_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc0_0_2_3 : (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_2 (fuseRow (0 : ZMod 8) (2 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 I) (ro (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 J) ee) (fuseCol (0 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_0_2 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 2) (ri (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 I) (ri (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc0_0_2_3 : (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 2).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_2 (fuseRow ((0 : ZMod 8) + 0) (2 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc0_0_2_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc0_0_2_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1]]]

noncomputable def Xcc0_0_2_3 : (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_2_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_2_3 : (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_2_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 4 = 4` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_2_3 : ∀ I J g, Xc0_0_2_3 I J g = Xcc0_0_2_3 I J g := by
  decide +kernel

theorem hYtabc0_0_2_3 : ∀ I J g, Yc0_0_2_3 I J g = Ycc0_0_2_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc0_0_2_3 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T0_0_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_2 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 2)) Xc0_0_2_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 hfuseZ_0_2 hfuseZ_0_2 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 2)) Xcc0_0_2_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2)) (realRepBasis ((0 : ZMod 8) + 0 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_2_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 2)) Yc0_0_2_3 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hfuseZ_0_2 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 2)) Ycc0_0_2_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 2).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 2).2)) (realRepBasis ((0 : ZMod 8) + 0 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_2_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 2) (realGauge.gaugeSizeL 0 0 2).1 (realGauge.gaugeSizeL 0 0 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_2_3 TL0_0_2 YLc0_0_2_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint0_0_2 (i : Fin (realRepDim (0 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (0 : ZMod 8) i)) * T0_0_2
      = ((sgn (realRepBasisParity (0 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T0_0_2 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (0 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 1 := i.isLt
  have h0 : (i : ℕ) = 0 := by omega
  rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) from Fin.ext h0]
  exact hinta0_0_2_0

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint0_0_2 (i : Fin (realRepDim (0 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (0 : ZMod 8) i)) * T0_0_2
      = ((sgn (realRepBasisParity (0 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T0_0_2 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (0 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 1 := i.isLt
  have h0 : (i : ℕ) = 0 := by omega
  rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) from Fin.ext h0]
  exact hintb0_0_2_0

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint0_0_2 (i : Fin (realRepDim (2 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) i)) * T0_0_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T0_0_2 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h0]; exact hintc0_0_2_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h1]; exact hintc0_0_2_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h2]; exact hintc0_0_2_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h3]; exact hintc0_0_2_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT0_0_2_mem_gInterSpace :
    gtOfT ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 T0_0_2 ∈ gInterSpace ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 hT0_0_2 hAint0_0_2 hBint0_0_2 hCint0_0_2

theorem gtOfT0_0_2_ne_zero : gtOfT ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 T0_0_2 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) hsz0_0_2 T0_0_2_ne_zero

theorem gInterSpace0_0_2_ne_bot : gInterSpace ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT0_0_2_mem_gInterSpace, gtOfT0_0_2_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_0_0_2 : gParity ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (2 : ZMod 8) gInterSpace0_0_2_ne_bot).symm

end Triple_0_0_2

/-! ### The triple `(0,0,3)`

`gaugeSizeL = gaugeSizeR = (1,0)`, `dim D_3 = 8`, certgen parity `0`; the unit-slot shortcut: the connector is the identity, so every certificate carries the sign `+1`. -/
section Triple_0_0_3
open Module
theorem hsz0_0_3 : realGauge.gaugeSizeR 0 0 3 = realGauge.gaugeSizeL 0 0 3 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`1 x 1 x 8`). -/
def TL0_0_3 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0]]]

/-- The same literal read at the composite frame `Fin 1 ⊕ Fin 0`. -/
noncomputable def Tc0_0_3 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun r s g => coeffGet TL0_0_3 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_3`. -/
noncomputable def T0_0_3 : ((realGauge.D ((0 : ZMod 8) + 0 + 3)).matrixSuper
    (realGauge.gaugeSizeL 0 0 3).1 (realGauge.gaugeSizeL 0 0 3).2).carrier :=
  matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Tc0_0_3

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT0_0_3 : T0_0_3 ∈ ((realGauge.D ((0 : ZMod 8) + 0 + 3)).matrixSuper
    (realGauge.gaugeSizeL 0 0 3).1 (realGauge.gaugeSizeL 0 0 3).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((0 : ZMod 8) + 0 + 3) Tc0_0_3 0 (by decide)

theorem T0_0_3_ne_zero : T0_0_3 ≠ 0 :=
  matOfCoeff_ne_zero ((0 : ZMod 8) + 0 + 3) Tc0_0_3 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa0_0_3_0 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun I J g => if (ro (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 I) = (ro (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (3 : ZMod 8)).1 (realSize (0 : ZMod 8) (3 : ZMod 8)).2 (ro (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 I)
          * realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_3 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 3) (ri (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 I) (ri (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya0_0_3_0 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_0 (fuseRow (0 : ZMod 8) (0 : ZMod 8) (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I) (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (0 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_0_3 (fuseRow ((0 : ZMod 8) + 0) (3 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa0_0_3_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa0_0_3_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca0_0_3_0 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa0_0_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca0_0_3_0 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa0_0_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 8 = 8` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba0_0_3_0 : ∀ I J g, Xa0_0_3_0 I J g = Xca0_0_3_0 I J g := by
  decide +kernel

theorem hYtaba0_0_3_0 : ∀ I J g, Ya0_0_3_0 I J g = Yca0_0_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta0_0_3_0 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))) * T0_0_3
      = ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_3 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Xa0_0_3_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 hfuseZ_0_3 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Xca0_0_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2)) (realRepBasis ((0 : ZMod 8) + 0 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba0_0_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Ya0_0_3_0 := Matrix.ext fun I J => routeL_aSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hfuseZ_0_0 hfuseZ_0_3 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Yca0_0_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2)) (realRepBasis ((0 : ZMod 8) + 0 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba0_0_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 3) (realGauge.gaugeSizeL 0 0 3).1 (realGauge.gaugeSizeL 0 0 3).2 ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa0_0_3_0 TL0_0_3 YLa0_0_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb0_0_3_0 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_3 (fuseRow (0 : ZMod 8) (3 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 I) (ro (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 J) ee) (fuseCol (0 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_0_3 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 3) (ri (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 I) (ri (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb0_0_3_0 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_0 (fuseRow (0 : ZMod 8) (0 : ZMod 8) (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I) (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (0 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_0_3 (fuseRow ((0 : ZMod 8) + 0) (3 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb0_0_3_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb0_0_3_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb0_0_3_0 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb0_0_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb0_0_3_0 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb0_0_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 8 = 8` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb0_0_3_0 : ∀ I J g, Xb0_0_3_0 I J g = Xcb0_0_3_0 I J g := by
  decide +kernel

theorem hYtabb0_0_3_0 : ∀ I J g, Yb0_0_3_0 I J g = Ycb0_0_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb0_0_3_0 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))) * T0_0_3
      = ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_3 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Xb0_0_3_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 hfuseZ_0_3 hfuseZ_0_3 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Xcb0_0_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2)) (realRepBasis ((0 : ZMod 8) + 0 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb0_0_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Yb0_0_3_0 := Matrix.ext fun I J => routeL_bSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hfuseZ_0_0 hfuseZ_0_3 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Ycb0_0_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2)) (realRepBasis ((0 : ZMod 8) + 0 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb0_0_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 3) (realGauge.gaugeSizeL 0 0 3).1 (realGauge.gaugeSizeL 0 0 3).2 ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb0_0_3_0 TL0_0_3 YLb0_0_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc0_0_3_0 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_3 (fuseRow (0 : ZMod 8) (3 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 I) (ro (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 J) ee) (fuseCol (0 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_0_3 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 3) (ri (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 I) (ri (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc0_0_3_0 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_3 (fuseRow ((0 : ZMod 8) + 0) (3 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc0_0_3_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc0_0_3_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcc0_0_3_0 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_3_0 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 8 = 8` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_3_0 : ∀ I J g, Xc0_0_3_0 I J g = Xcc0_0_3_0 I J g := by
  decide +kernel

theorem hYtabc0_0_3_0 : ∀ I J g, Yc0_0_3_0 I J g = Ycc0_0_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc0_0_3_0 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T0_0_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_3 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Xc0_0_3_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 hfuseZ_0_3 hfuseZ_0_3 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Xcc0_0_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2)) (realRepBasis ((0 : ZMod 8) + 0 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Yc0_0_3_0 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hfuseZ_0_3 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Ycc0_0_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2)) (realRepBasis ((0 : ZMod 8) + 0 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 3) (realGauge.gaugeSizeL 0 0 3).1 (realGauge.gaugeSizeL 0 0 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_3_0 TL0_0_3 YLc0_0_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc0_0_3_1 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_3 (fuseRow (0 : ZMod 8) (3 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 I) (ro (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 J) ee) (fuseCol (0 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_0_3 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 3) (ri (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 I) (ri (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc0_0_3_1 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_3 (fuseRow ((0 : ZMod 8) + 0) (3 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc0_0_3_1 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc0_0_3_1 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcc0_0_3_1 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_3_1 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 8 = 8` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_3_1 : ∀ I J g, Xc0_0_3_1 I J g = Xcc0_0_3_1 I J g := by
  decide +kernel

theorem hYtabc0_0_3_1 : ∀ I J g, Yc0_0_3_1 I J g = Ycc0_0_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc0_0_3_1 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T0_0_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_3 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Xc0_0_3_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 hfuseZ_0_3 hfuseZ_0_3 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Xcc0_0_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2)) (realRepBasis ((0 : ZMod 8) + 0 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Yc0_0_3_1 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hfuseZ_0_3 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Ycc0_0_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2)) (realRepBasis ((0 : ZMod 8) + 0 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 3) (realGauge.gaugeSizeL 0 0 3).1 (realGauge.gaugeSizeL 0 0 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_3_1 TL0_0_3 YLc0_0_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc0_0_3_2 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_3 (fuseRow (0 : ZMod 8) (3 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 I) (ro (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 J) ee) (fuseCol (0 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_0_3 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 3) (ri (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 I) (ri (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc0_0_3_2 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_3 (fuseRow ((0 : ZMod 8) + 0) (3 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc0_0_3_2 : List (List (List ℤ)) :=
  [[[0, 0, 1, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc0_0_3_2 : List (List (List ℤ)) :=
  [[[0, 0, 1, 0, 0, 0, 0, 0]]]

noncomputable def Xcc0_0_3_2 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_3_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_3_2 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_3_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 8 = 8` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_3_2 : ∀ I J g, Xc0_0_3_2 I J g = Xcc0_0_3_2 I J g := by
  decide +kernel

theorem hYtabc0_0_3_2 : ∀ I J g, Yc0_0_3_2 I J g = Ycc0_0_3_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc0_0_3_2 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T0_0_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_3 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Xc0_0_3_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 hfuseZ_0_3 hfuseZ_0_3 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Xcc0_0_3_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2)) (realRepBasis ((0 : ZMod 8) + 0 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_3_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Yc0_0_3_2 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hfuseZ_0_3 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Ycc0_0_3_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2)) (realRepBasis ((0 : ZMod 8) + 0 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_3_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 3) (realGauge.gaugeSizeL 0 0 3).1 (realGauge.gaugeSizeL 0 0 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_3_2 TL0_0_3 YLc0_0_3_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc0_0_3_3 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_3 (fuseRow (0 : ZMod 8) (3 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 I) (ro (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 J) ee) (fuseCol (0 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_0_3 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 3) (ri (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 I) (ri (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc0_0_3_3 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_3 (fuseRow ((0 : ZMod 8) + 0) (3 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc0_0_3_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc0_0_3_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1, 0, 0, 0, 0]]]

noncomputable def Xcc0_0_3_3 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_3_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_3_3 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_3_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 8 = 8` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_3_3 : ∀ I J g, Xc0_0_3_3 I J g = Xcc0_0_3_3 I J g := by
  decide +kernel

theorem hYtabc0_0_3_3 : ∀ I J g, Yc0_0_3_3 I J g = Ycc0_0_3_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc0_0_3_3 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T0_0_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_3 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Xc0_0_3_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 hfuseZ_0_3 hfuseZ_0_3 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Xcc0_0_3_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2)) (realRepBasis ((0 : ZMod 8) + 0 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_3_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Yc0_0_3_3 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hfuseZ_0_3 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Ycc0_0_3_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2)) (realRepBasis ((0 : ZMod 8) + 0 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_3_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 3) (realGauge.gaugeSizeL 0 0 3).1 (realGauge.gaugeSizeL 0 0 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_3_3 TL0_0_3 YLc0_0_3_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Xc0_0_3_4 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_3 (fuseRow (0 : ZMod 8) (3 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 I) (ro (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 J) ee) (fuseCol (0 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_0_3 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 3) (ri (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 I) (ri (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Yc0_0_3_4 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_3 (fuseRow ((0 : ZMod 8) + 0) (3 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `4`, pre-tabulated. -/
def XLc0_0_3_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 1, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `4`, pre-tabulated. -/
def YLc0_0_3_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 1, 0, 0, 0]]]

noncomputable def Xcc0_0_3_4 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_3_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_3_4 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_3_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 8 = 8` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_3_4 : ∀ I J g, Xc0_0_3_4 I J g = Xcc0_0_3_4 I J g := by
  decide +kernel

theorem hYtabc0_0_3_4 : ∀ I J g, Yc0_0_3_4 I J g = Ycc0_0_3_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `4`** (Koszul sign `+1`). -/
theorem hintc0_0_3_4 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T0_0_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_3 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Xc0_0_3_4 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 hfuseZ_0_3 hfuseZ_0_3 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Xcc0_0_3_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2)) (realRepBasis ((0 : ZMod 8) + 0 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_3_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Yc0_0_3_4 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hfuseZ_0_3 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Ycc0_0_3_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2)) (realRepBasis ((0 : ZMod 8) + 0 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_3_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 3) (realGauge.gaugeSizeL 0 0 3).1 (realGauge.gaugeSizeL 0 0 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_3_4 TL0_0_3 YLc0_0_3_4 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Xc0_0_3_5 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_3 (fuseRow (0 : ZMod 8) (3 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 I) (ro (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 J) ee) (fuseCol (0 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_0_3 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 3) (ri (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 I) (ri (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Yc0_0_3_5 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_3 (fuseRow ((0 : ZMod 8) + 0) (3 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `5`, pre-tabulated. -/
def XLc0_0_3_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 1, 0, 0]]]

/-- Left route at the `c`-slot generator `5`, pre-tabulated. -/
def YLc0_0_3_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 1, 0, 0]]]

noncomputable def Xcc0_0_3_5 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_3_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_3_5 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_3_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 8 = 8` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_3_5 : ∀ I J g, Xc0_0_3_5 I J g = Xcc0_0_3_5 I J g := by
  decide +kernel

theorem hYtabc0_0_3_5 : ∀ I J g, Yc0_0_3_5 I J g = Ycc0_0_3_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintc0_0_3_5 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T0_0_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_3 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Xc0_0_3_5 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 hfuseZ_0_3 hfuseZ_0_3 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Xcc0_0_3_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2)) (realRepBasis ((0 : ZMod 8) + 0 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_3_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Yc0_0_3_5 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hfuseZ_0_3 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Ycc0_0_3_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2)) (realRepBasis ((0 : ZMod 8) + 0 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_3_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 3) (realGauge.gaugeSizeL 0 0 3).1 (realGauge.gaugeSizeL 0 0 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_3_5 TL0_0_3 YLc0_0_3_5 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Xc0_0_3_6 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_3 (fuseRow (0 : ZMod 8) (3 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 I) (ro (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 J) ee) (fuseCol (0 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_0_3 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 3) (ri (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 I) (ri (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Yc0_0_3_6 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_3 (fuseRow ((0 : ZMod 8) + 0) (3 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `6`, pre-tabulated. -/
def XLc0_0_3_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 1, 0]]]

/-- Left route at the `c`-slot generator `6`, pre-tabulated. -/
def YLc0_0_3_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 1, 0]]]

noncomputable def Xcc0_0_3_6 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_3_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_3_6 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_3_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 8 = 8` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_3_6 : ∀ I J g, Xc0_0_3_6 I J g = Xcc0_0_3_6 I J g := by
  decide +kernel

theorem hYtabc0_0_3_6 : ∀ I J g, Yc0_0_3_6 I J g = Ycc0_0_3_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintc0_0_3_6 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T0_0_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_3 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Xc0_0_3_6 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 hfuseZ_0_3 hfuseZ_0_3 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Xcc0_0_3_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2)) (realRepBasis ((0 : ZMod 8) + 0 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_3_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Yc0_0_3_6 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hfuseZ_0_3 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Ycc0_0_3_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2)) (realRepBasis ((0 : ZMod 8) + 0 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_3_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 3) (realGauge.gaugeSizeL 0 0 3).1 (realGauge.gaugeSizeL 0 0 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_3_6 TL0_0_3 YLc0_0_3_6 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Xc0_0_3_7 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_3 (fuseRow (0 : ZMod 8) (3 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 I) (ro (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 J) ee) (fuseCol (0 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_0_3 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 3) (ri (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 I) (ri (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Yc0_0_3_7 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_3 (fuseRow ((0 : ZMod 8) + 0) (3 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `7`, pre-tabulated. -/
def XLc0_0_3_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 1]]]

/-- Left route at the `c`-slot generator `7`, pre-tabulated. -/
def YLc0_0_3_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 1]]]

noncomputable def Xcc0_0_3_7 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_3_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_3_7 : (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_3_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 8 = 8` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_3_7 : ∀ I J g, Xc0_0_3_7 I J g = Xcc0_0_3_7 I J g := by
  decide +kernel

theorem hYtabc0_0_3_7 : ∀ I J g, Yc0_0_3_7 I J g = Ycc0_0_3_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `7`** (Koszul sign `+1`). -/
theorem hintc0_0_3_7 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T0_0_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_3 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Xc0_0_3_7 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 hfuseZ_0_3 hfuseZ_0_3 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Xcc0_0_3_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2)) (realRepBasis ((0 : ZMod 8) + 0 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_3_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Yc0_0_3_7 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hfuseZ_0_3 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 3)) Ycc0_0_3_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 3).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 3).2)) (realRepBasis ((0 : ZMod 8) + 0 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_3_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 3) (realGauge.gaugeSizeL 0 0 3).1 (realGauge.gaugeSizeL 0 0 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_3_7 TL0_0_3 YLc0_0_3_7 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint0_0_3 (i : Fin (realRepDim (0 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (0 : ZMod 8) i)) * T0_0_3
      = ((sgn (realRepBasisParity (0 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T0_0_3 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (0 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 1 := i.isLt
  have h0 : (i : ℕ) = 0 := by omega
  rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) from Fin.ext h0]
  exact hinta0_0_3_0

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint0_0_3 (i : Fin (realRepDim (0 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (0 : ZMod 8) i)) * T0_0_3
      = ((sgn (realRepBasisParity (0 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T0_0_3 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (0 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 1 := i.isLt
  have h0 : (i : ℕ) = 0 := by omega
  rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) from Fin.ext h0]
  exact hintb0_0_3_0

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint0_0_3 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T0_0_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T0_0_3 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hintc0_0_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hintc0_0_3_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hintc0_0_3_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hintc0_0_3_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hintc0_0_3_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hintc0_0_3_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hintc0_0_3_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hintc0_0_3_7

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT0_0_3_mem_gInterSpace :
    gtOfT ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 T0_0_3 ∈ gInterSpace ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 hT0_0_3 hAint0_0_3 hBint0_0_3 hCint0_0_3

theorem gtOfT0_0_3_ne_zero : gtOfT ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 T0_0_3 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) hsz0_0_3 T0_0_3_ne_zero

theorem gInterSpace0_0_3_ne_bot : gInterSpace ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT0_0_3_mem_gInterSpace, gtOfT0_0_3_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_0_0_3 : gParity ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (3 : ZMod 8) gInterSpace0_0_3_ne_bot).symm

end Triple_0_0_3

/-! ### The triple `(0,0,4)`

`gaugeSizeL = gaugeSizeR = (1,0)`, `dim D_4 = 4`, certgen parity `0`; the unit-slot shortcut: the connector is the identity, so every certificate carries the sign `+1`. -/
section Triple_0_0_4
open Module
theorem hsz0_0_4 : realGauge.gaugeSizeR 0 0 4 = realGauge.gaugeSizeL 0 0 4 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`1 x 1 x 4`). -/
def TL0_0_4 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0]]]

/-- The same literal read at the composite frame `Fin 1 ⊕ Fin 0`. -/
noncomputable def Tc0_0_4 : (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 4).val) → ℤ :=
  fun r s g => coeffGet TL0_0_4 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_4`. -/
noncomputable def T0_0_4 : ((realGauge.D ((0 : ZMod 8) + 0 + 4)).matrixSuper
    (realGauge.gaugeSizeL 0 0 4).1 (realGauge.gaugeSizeL 0 0 4).2).carrier :=
  matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 4)) Tc0_0_4

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT0_0_4 : T0_0_4 ∈ ((realGauge.D ((0 : ZMod 8) + 0 + 4)).matrixSuper
    (realGauge.gaugeSizeL 0 0 4).1 (realGauge.gaugeSizeL 0 0 4).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((0 : ZMod 8) + 0 + 4) Tc0_0_4 0 (by decide)

theorem T0_0_4_ne_zero : T0_0_4 ≠ 0 :=
  matOfCoeff_ne_zero ((0 : ZMod 8) + 0 + 4) Tc0_0_4 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa0_0_4_0 : (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 4).val) → ℤ :=
  fun I J g => if (ro (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 I) = (ro (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (4 : ZMod 8)).1 (realSize (0 : ZMod 8) (4 : ZMod 8)).2 (ro (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 I)
          * realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_4 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 4) (ri (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 I) (ri (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya0_0_4_0 : (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_0 (fuseRow (0 : ZMod 8) (0 : ZMod 8) (lo (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) I) (lo (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (0 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_0_4 (fuseRow ((0 : ZMod 8) + 0) (4 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa0_0_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa0_0_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0]]]

noncomputable def Xca0_0_4_0 : (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa0_0_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca0_0_4_0 : (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa0_0_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 4 = 4` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba0_0_4_0 : ∀ I J g, Xa0_0_4_0 I J g = Xca0_0_4_0 I J g := by
  decide +kernel

theorem hYtaba0_0_4_0 : ∀ I J g, Ya0_0_4_0 I J g = Yca0_0_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta0_0_4_0 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))) * T0_0_4
      = ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_4 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 4)) Xa0_0_4_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 hfuseZ_0_4 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 4)) Xca0_0_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2)) (realRepBasis ((0 : ZMod 8) + 0 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba0_0_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 4)) Ya0_0_4_0 := Matrix.ext fun I J => routeL_aSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hfuseZ_0_0 hfuseZ_0_4 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 4)) Yca0_0_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2)) (realRepBasis ((0 : ZMod 8) + 0 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba0_0_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 4) (realGauge.gaugeSizeL 0 0 4).1 (realGauge.gaugeSizeL 0 0 4).2 ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa0_0_4_0 TL0_0_4 YLa0_0_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb0_0_4_0 : (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_4 (fuseRow (0 : ZMod 8) (4 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 I) (ro (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 J) ee) (fuseCol (0 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_0_4 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 4) (ri (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 I) (ri (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb0_0_4_0 : (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_0 (fuseRow (0 : ZMod 8) (0 : ZMod 8) (lo (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) I) (lo (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (0 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_0_4 (fuseRow ((0 : ZMod 8) + 0) (4 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb0_0_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb0_0_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0]]]

noncomputable def Xcb0_0_4_0 : (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb0_0_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb0_0_4_0 : (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb0_0_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 4 = 4` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb0_0_4_0 : ∀ I J g, Xb0_0_4_0 I J g = Xcb0_0_4_0 I J g := by
  decide +kernel

theorem hYtabb0_0_4_0 : ∀ I J g, Yb0_0_4_0 I J g = Ycb0_0_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb0_0_4_0 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))) * T0_0_4
      = ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_4 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 4)) Xb0_0_4_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 hfuseZ_0_4 hfuseZ_0_4 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 4)) Xcb0_0_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2)) (realRepBasis ((0 : ZMod 8) + 0 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb0_0_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 4)) Yb0_0_4_0 := Matrix.ext fun I J => routeL_bSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hfuseZ_0_0 hfuseZ_0_4 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 4)) Ycb0_0_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2)) (realRepBasis ((0 : ZMod 8) + 0 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb0_0_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 4) (realGauge.gaugeSizeL 0 0 4).1 (realGauge.gaugeSizeL 0 0 4).2 ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb0_0_4_0 TL0_0_4 YLb0_0_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc0_0_4_0 : (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_4 (fuseRow (0 : ZMod 8) (4 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 I) (ro (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 J) ee) (fuseCol (0 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_0_4 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 4) (ri (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 I) (ri (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc0_0_4_0 : (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 4).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_4 (fuseRow ((0 : ZMod 8) + 0) (4 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc0_0_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc0_0_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0]]]

noncomputable def Xcc0_0_4_0 : (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_4_0 : (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 4 = 4` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_4_0 : ∀ I J g, Xc0_0_4_0 I J g = Xcc0_0_4_0 I J g := by
  decide +kernel

theorem hYtabc0_0_4_0 : ∀ I J g, Yc0_0_4_0 I J g = Ycc0_0_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc0_0_4_0 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T0_0_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_4 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 4)) Xc0_0_4_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 hfuseZ_0_4 hfuseZ_0_4 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 4)) Xcc0_0_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2)) (realRepBasis ((0 : ZMod 8) + 0 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 4)) Yc0_0_4_0 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hfuseZ_0_4 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 4)) Ycc0_0_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2)) (realRepBasis ((0 : ZMod 8) + 0 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 4) (realGauge.gaugeSizeL 0 0 4).1 (realGauge.gaugeSizeL 0 0 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_4_0 TL0_0_4 YLc0_0_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc0_0_4_1 : (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_4 (fuseRow (0 : ZMod 8) (4 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 I) (ro (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 J) ee) (fuseCol (0 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_0_4 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 4) (ri (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 I) (ri (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc0_0_4_1 : (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 4).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_4 (fuseRow ((0 : ZMod 8) + 0) (4 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc0_0_4_1 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc0_0_4_1 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0]]]

noncomputable def Xcc0_0_4_1 : (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_4_1 : (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 4 = 4` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_4_1 : ∀ I J g, Xc0_0_4_1 I J g = Xcc0_0_4_1 I J g := by
  decide +kernel

theorem hYtabc0_0_4_1 : ∀ I J g, Yc0_0_4_1 I J g = Ycc0_0_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc0_0_4_1 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T0_0_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_4 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 4)) Xc0_0_4_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 hfuseZ_0_4 hfuseZ_0_4 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 4)) Xcc0_0_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2)) (realRepBasis ((0 : ZMod 8) + 0 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 4)) Yc0_0_4_1 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hfuseZ_0_4 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 4)) Ycc0_0_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2)) (realRepBasis ((0 : ZMod 8) + 0 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 4) (realGauge.gaugeSizeL 0 0 4).1 (realGauge.gaugeSizeL 0 0 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_4_1 TL0_0_4 YLc0_0_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc0_0_4_2 : (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_4 (fuseRow (0 : ZMod 8) (4 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 I) (ro (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 J) ee) (fuseCol (0 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_0_4 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 4) (ri (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 I) (ri (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc0_0_4_2 : (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 4).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_4 (fuseRow ((0 : ZMod 8) + 0) (4 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc0_0_4_2 : List (List (List ℤ)) :=
  [[[0, 0, 1, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc0_0_4_2 : List (List (List ℤ)) :=
  [[[0, 0, 1, 0]]]

noncomputable def Xcc0_0_4_2 : (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_4_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_4_2 : (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_4_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 4 = 4` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_4_2 : ∀ I J g, Xc0_0_4_2 I J g = Xcc0_0_4_2 I J g := by
  decide +kernel

theorem hYtabc0_0_4_2 : ∀ I J g, Yc0_0_4_2 I J g = Ycc0_0_4_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc0_0_4_2 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T0_0_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_4 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 4)) Xc0_0_4_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 hfuseZ_0_4 hfuseZ_0_4 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 4)) Xcc0_0_4_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2)) (realRepBasis ((0 : ZMod 8) + 0 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_4_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 4)) Yc0_0_4_2 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hfuseZ_0_4 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 4)) Ycc0_0_4_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2)) (realRepBasis ((0 : ZMod 8) + 0 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_4_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 4) (realGauge.gaugeSizeL 0 0 4).1 (realGauge.gaugeSizeL 0 0 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_4_2 TL0_0_4 YLc0_0_4_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc0_0_4_3 : (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_4 (fuseRow (0 : ZMod 8) (4 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 I) (ro (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 J) ee) (fuseCol (0 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_0_4 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 4) (ri (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 I) (ri (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc0_0_4_3 : (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 4).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_4 (fuseRow ((0 : ZMod 8) + 0) (4 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc0_0_4_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc0_0_4_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1]]]

noncomputable def Xcc0_0_4_3 : (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_4_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_4_3 : (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_4_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 4 = 4` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_4_3 : ∀ I J g, Xc0_0_4_3 I J g = Xcc0_0_4_3 I J g := by
  decide +kernel

theorem hYtabc0_0_4_3 : ∀ I J g, Yc0_0_4_3 I J g = Ycc0_0_4_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc0_0_4_3 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T0_0_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_4 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 4)) Xc0_0_4_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 hfuseZ_0_4 hfuseZ_0_4 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 4)) Xcc0_0_4_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2)) (realRepBasis ((0 : ZMod 8) + 0 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_4_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 4)) Yc0_0_4_3 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hfuseZ_0_4 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 4)) Ycc0_0_4_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 4).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 4).2)) (realRepBasis ((0 : ZMod 8) + 0 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_4_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 4) (realGauge.gaugeSizeL 0 0 4).1 (realGauge.gaugeSizeL 0 0 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_4_3 TL0_0_4 YLc0_0_4_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint0_0_4 (i : Fin (realRepDim (0 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (0 : ZMod 8) i)) * T0_0_4
      = ((sgn (realRepBasisParity (0 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T0_0_4 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (0 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 1 := i.isLt
  have h0 : (i : ℕ) = 0 := by omega
  rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) from Fin.ext h0]
  exact hinta0_0_4_0

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint0_0_4 (i : Fin (realRepDim (0 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (0 : ZMod 8) i)) * T0_0_4
      = ((sgn (realRepBasisParity (0 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T0_0_4 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (0 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 1 := i.isLt
  have h0 : (i : ℕ) = 0 := by omega
  rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) from Fin.ext h0]
  exact hintb0_0_4_0

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint0_0_4 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T0_0_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T0_0_4 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hintc0_0_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hintc0_0_4_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hintc0_0_4_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hintc0_0_4_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT0_0_4_mem_gInterSpace :
    gtOfT ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 T0_0_4 ∈ gInterSpace ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 hT0_0_4 hAint0_0_4 hBint0_0_4 hCint0_0_4

theorem gtOfT0_0_4_ne_zero : gtOfT ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 T0_0_4 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) hsz0_0_4 T0_0_4_ne_zero

theorem gInterSpace0_0_4_ne_bot : gInterSpace ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT0_0_4_mem_gInterSpace, gtOfT0_0_4_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_0_0_4 : gParity ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (4 : ZMod 8) gInterSpace0_0_4_ne_bot).symm

end Triple_0_0_4

/-! ### The triple `(0,0,5)`

`gaugeSizeL = gaugeSizeR = (1,0)`, `dim D_5 = 8`, certgen parity `0`; the unit-slot shortcut: the connector is the identity, so every certificate carries the sign `+1`. -/
section Triple_0_0_5
open Module
theorem hsz0_0_5 : realGauge.gaugeSizeR 0 0 5 = realGauge.gaugeSizeL 0 0 5 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`1 x 1 x 8`). -/
def TL0_0_5 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0]]]

/-- The same literal read at the composite frame `Fin 1 ⊕ Fin 0`. -/
noncomputable def Tc0_0_5 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun r s g => coeffGet TL0_0_5 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_5`. -/
noncomputable def T0_0_5 : ((realGauge.D ((0 : ZMod 8) + 0 + 5)).matrixSuper
    (realGauge.gaugeSizeL 0 0 5).1 (realGauge.gaugeSizeL 0 0 5).2).carrier :=
  matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Tc0_0_5

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT0_0_5 : T0_0_5 ∈ ((realGauge.D ((0 : ZMod 8) + 0 + 5)).matrixSuper
    (realGauge.gaugeSizeL 0 0 5).1 (realGauge.gaugeSizeL 0 0 5).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((0 : ZMod 8) + 0 + 5) Tc0_0_5 0 (by decide)

theorem T0_0_5_ne_zero : T0_0_5 ≠ 0 :=
  matOfCoeff_ne_zero ((0 : ZMod 8) + 0 + 5) Tc0_0_5 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa0_0_5_0 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun I J g => if (ro (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 I) = (ro (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (5 : ZMod 8)).1 (realSize (0 : ZMod 8) (5 : ZMod 8)).2 (ro (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 I)
          * realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_5 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 5) (ri (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 I) (ri (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya0_0_5_0 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_0 (fuseRow (0 : ZMod 8) (0 : ZMod 8) (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I) (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (0 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_0_5 (fuseRow ((0 : ZMod 8) + 0) (5 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa0_0_5_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa0_0_5_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca0_0_5_0 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa0_0_5_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca0_0_5_0 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa0_0_5_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 8 = 8` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba0_0_5_0 : ∀ I J g, Xa0_0_5_0 I J g = Xca0_0_5_0 I J g := by
  decide +kernel

theorem hYtaba0_0_5_0 : ∀ I J g, Ya0_0_5_0 I J g = Yca0_0_5_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta0_0_5_0 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))) * T0_0_5
      = ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_5 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Xa0_0_5_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 hfuseZ_0_5 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Xca0_0_5_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2)) (realRepBasis ((0 : ZMod 8) + 0 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba0_0_5_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Ya0_0_5_0 := Matrix.ext fun I J => routeL_aSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hfuseZ_0_0 hfuseZ_0_5 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Yca0_0_5_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2)) (realRepBasis ((0 : ZMod 8) + 0 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba0_0_5_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 5) (realGauge.gaugeSizeL 0 0 5).1 (realGauge.gaugeSizeL 0 0 5).2 ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa0_0_5_0 TL0_0_5 YLa0_0_5_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb0_0_5_0 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_5 (fuseRow (0 : ZMod 8) (5 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 I) (ro (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 J) ee) (fuseCol (0 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_0_5 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 5) (ri (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 I) (ri (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb0_0_5_0 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_0 (fuseRow (0 : ZMod 8) (0 : ZMod 8) (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I) (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (0 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_0_5 (fuseRow ((0 : ZMod 8) + 0) (5 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb0_0_5_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb0_0_5_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb0_0_5_0 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb0_0_5_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb0_0_5_0 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb0_0_5_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 8 = 8` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb0_0_5_0 : ∀ I J g, Xb0_0_5_0 I J g = Xcb0_0_5_0 I J g := by
  decide +kernel

theorem hYtabb0_0_5_0 : ∀ I J g, Yb0_0_5_0 I J g = Ycb0_0_5_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb0_0_5_0 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))) * T0_0_5
      = ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_5 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Xb0_0_5_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 hfuseZ_0_5 hfuseZ_0_5 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Xcb0_0_5_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2)) (realRepBasis ((0 : ZMod 8) + 0 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb0_0_5_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Yb0_0_5_0 := Matrix.ext fun I J => routeL_bSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hfuseZ_0_0 hfuseZ_0_5 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Ycb0_0_5_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2)) (realRepBasis ((0 : ZMod 8) + 0 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb0_0_5_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 5) (realGauge.gaugeSizeL 0 0 5).1 (realGauge.gaugeSizeL 0 0 5).2 ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb0_0_5_0 TL0_0_5 YLb0_0_5_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc0_0_5_0 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_5 (fuseRow (0 : ZMod 8) (5 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 I) (ro (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 J) ee) (fuseCol (0 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_0_5 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 5) (ri (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 I) (ri (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc0_0_5_0 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_5 (fuseRow ((0 : ZMod 8) + 0) (5 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc0_0_5_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc0_0_5_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcc0_0_5_0 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_5_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_5_0 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_5_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 8 = 8` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_5_0 : ∀ I J g, Xc0_0_5_0 I J g = Xcc0_0_5_0 I J g := by
  decide +kernel

theorem hYtabc0_0_5_0 : ∀ I J g, Yc0_0_5_0 I J g = Ycc0_0_5_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc0_0_5_0 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T0_0_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_5 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Xc0_0_5_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 hfuseZ_0_5 hfuseZ_0_5 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Xcc0_0_5_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2)) (realRepBasis ((0 : ZMod 8) + 0 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_5_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Yc0_0_5_0 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hfuseZ_0_5 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Ycc0_0_5_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2)) (realRepBasis ((0 : ZMod 8) + 0 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_5_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 5) (realGauge.gaugeSizeL 0 0 5).1 (realGauge.gaugeSizeL 0 0 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_5_0 TL0_0_5 YLc0_0_5_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc0_0_5_1 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_5 (fuseRow (0 : ZMod 8) (5 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 I) (ro (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 J) ee) (fuseCol (0 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_0_5 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 5) (ri (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 I) (ri (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc0_0_5_1 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_5 (fuseRow ((0 : ZMod 8) + 0) (5 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc0_0_5_1 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc0_0_5_1 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcc0_0_5_1 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_5_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_5_1 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_5_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 8 = 8` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_5_1 : ∀ I J g, Xc0_0_5_1 I J g = Xcc0_0_5_1 I J g := by
  decide +kernel

theorem hYtabc0_0_5_1 : ∀ I J g, Yc0_0_5_1 I J g = Ycc0_0_5_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc0_0_5_1 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T0_0_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_5 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Xc0_0_5_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 hfuseZ_0_5 hfuseZ_0_5 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Xcc0_0_5_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2)) (realRepBasis ((0 : ZMod 8) + 0 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_5_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Yc0_0_5_1 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hfuseZ_0_5 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Ycc0_0_5_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2)) (realRepBasis ((0 : ZMod 8) + 0 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_5_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 5) (realGauge.gaugeSizeL 0 0 5).1 (realGauge.gaugeSizeL 0 0 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_5_1 TL0_0_5 YLc0_0_5_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc0_0_5_2 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_5 (fuseRow (0 : ZMod 8) (5 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 I) (ro (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 J) ee) (fuseCol (0 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_0_5 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 5) (ri (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 I) (ri (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc0_0_5_2 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_5 (fuseRow ((0 : ZMod 8) + 0) (5 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc0_0_5_2 : List (List (List ℤ)) :=
  [[[0, 0, 1, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc0_0_5_2 : List (List (List ℤ)) :=
  [[[0, 0, 1, 0, 0, 0, 0, 0]]]

noncomputable def Xcc0_0_5_2 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_5_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_5_2 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_5_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 8 = 8` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_5_2 : ∀ I J g, Xc0_0_5_2 I J g = Xcc0_0_5_2 I J g := by
  decide +kernel

theorem hYtabc0_0_5_2 : ∀ I J g, Yc0_0_5_2 I J g = Ycc0_0_5_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc0_0_5_2 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T0_0_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_5 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Xc0_0_5_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 hfuseZ_0_5 hfuseZ_0_5 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Xcc0_0_5_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2)) (realRepBasis ((0 : ZMod 8) + 0 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_5_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Yc0_0_5_2 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hfuseZ_0_5 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Ycc0_0_5_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2)) (realRepBasis ((0 : ZMod 8) + 0 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_5_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 5) (realGauge.gaugeSizeL 0 0 5).1 (realGauge.gaugeSizeL 0 0 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_5_2 TL0_0_5 YLc0_0_5_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc0_0_5_3 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_5 (fuseRow (0 : ZMod 8) (5 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 I) (ro (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 J) ee) (fuseCol (0 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_0_5 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 5) (ri (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 I) (ri (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc0_0_5_3 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_5 (fuseRow ((0 : ZMod 8) + 0) (5 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc0_0_5_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc0_0_5_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1, 0, 0, 0, 0]]]

noncomputable def Xcc0_0_5_3 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_5_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_5_3 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_5_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 8 = 8` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_5_3 : ∀ I J g, Xc0_0_5_3 I J g = Xcc0_0_5_3 I J g := by
  decide +kernel

theorem hYtabc0_0_5_3 : ∀ I J g, Yc0_0_5_3 I J g = Ycc0_0_5_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc0_0_5_3 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T0_0_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_5 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Xc0_0_5_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 hfuseZ_0_5 hfuseZ_0_5 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Xcc0_0_5_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2)) (realRepBasis ((0 : ZMod 8) + 0 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_5_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Yc0_0_5_3 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hfuseZ_0_5 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Ycc0_0_5_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2)) (realRepBasis ((0 : ZMod 8) + 0 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_5_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 5) (realGauge.gaugeSizeL 0 0 5).1 (realGauge.gaugeSizeL 0 0 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_5_3 TL0_0_5 YLc0_0_5_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Xc0_0_5_4 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_5 (fuseRow (0 : ZMod 8) (5 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 I) (ro (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 J) ee) (fuseCol (0 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_0_5 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 5) (ri (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 I) (ri (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Yc0_0_5_4 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_5 (fuseRow ((0 : ZMod 8) + 0) (5 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `4`, pre-tabulated. -/
def XLc0_0_5_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 1, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `4`, pre-tabulated. -/
def YLc0_0_5_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 1, 0, 0, 0]]]

noncomputable def Xcc0_0_5_4 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_5_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_5_4 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_5_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 8 = 8` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_5_4 : ∀ I J g, Xc0_0_5_4 I J g = Xcc0_0_5_4 I J g := by
  decide +kernel

theorem hYtabc0_0_5_4 : ∀ I J g, Yc0_0_5_4 I J g = Ycc0_0_5_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `4`** (Koszul sign `+1`). -/
theorem hintc0_0_5_4 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T0_0_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_5 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Xc0_0_5_4 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 hfuseZ_0_5 hfuseZ_0_5 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Xcc0_0_5_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2)) (realRepBasis ((0 : ZMod 8) + 0 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_5_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Yc0_0_5_4 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hfuseZ_0_5 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Ycc0_0_5_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2)) (realRepBasis ((0 : ZMod 8) + 0 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_5_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 5) (realGauge.gaugeSizeL 0 0 5).1 (realGauge.gaugeSizeL 0 0 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_5_4 TL0_0_5 YLc0_0_5_4 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Xc0_0_5_5 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_5 (fuseRow (0 : ZMod 8) (5 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 I) (ro (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 J) ee) (fuseCol (0 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_0_5 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 5) (ri (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 I) (ri (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Yc0_0_5_5 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_5 (fuseRow ((0 : ZMod 8) + 0) (5 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `5`, pre-tabulated. -/
def XLc0_0_5_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 1, 0, 0]]]

/-- Left route at the `c`-slot generator `5`, pre-tabulated. -/
def YLc0_0_5_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 1, 0, 0]]]

noncomputable def Xcc0_0_5_5 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_5_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_5_5 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_5_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 8 = 8` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_5_5 : ∀ I J g, Xc0_0_5_5 I J g = Xcc0_0_5_5 I J g := by
  decide +kernel

theorem hYtabc0_0_5_5 : ∀ I J g, Yc0_0_5_5 I J g = Ycc0_0_5_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintc0_0_5_5 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T0_0_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_5 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Xc0_0_5_5 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 hfuseZ_0_5 hfuseZ_0_5 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Xcc0_0_5_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2)) (realRepBasis ((0 : ZMod 8) + 0 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_5_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Yc0_0_5_5 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hfuseZ_0_5 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Ycc0_0_5_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2)) (realRepBasis ((0 : ZMod 8) + 0 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_5_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 5) (realGauge.gaugeSizeL 0 0 5).1 (realGauge.gaugeSizeL 0 0 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_5_5 TL0_0_5 YLc0_0_5_5 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Xc0_0_5_6 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_5 (fuseRow (0 : ZMod 8) (5 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 I) (ro (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 J) ee) (fuseCol (0 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_0_5 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 5) (ri (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 I) (ri (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Yc0_0_5_6 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_5 (fuseRow ((0 : ZMod 8) + 0) (5 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `6`, pre-tabulated. -/
def XLc0_0_5_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 1, 0]]]

/-- Left route at the `c`-slot generator `6`, pre-tabulated. -/
def YLc0_0_5_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 1, 0]]]

noncomputable def Xcc0_0_5_6 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_5_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_5_6 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_5_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 8 = 8` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_5_6 : ∀ I J g, Xc0_0_5_6 I J g = Xcc0_0_5_6 I J g := by
  decide +kernel

theorem hYtabc0_0_5_6 : ∀ I J g, Yc0_0_5_6 I J g = Ycc0_0_5_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintc0_0_5_6 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T0_0_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_5 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Xc0_0_5_6 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 hfuseZ_0_5 hfuseZ_0_5 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Xcc0_0_5_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2)) (realRepBasis ((0 : ZMod 8) + 0 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_5_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Yc0_0_5_6 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hfuseZ_0_5 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Ycc0_0_5_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2)) (realRepBasis ((0 : ZMod 8) + 0 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_5_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 5) (realGauge.gaugeSizeL 0 0 5).1 (realGauge.gaugeSizeL 0 0 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_5_6 TL0_0_5 YLc0_0_5_6 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Xc0_0_5_7 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_5 (fuseRow (0 : ZMod 8) (5 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 I) (ro (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 J) ee) (fuseCol (0 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_0_5 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 5) (ri (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 I) (ri (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Yc0_0_5_7 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_5 (fuseRow ((0 : ZMod 8) + 0) (5 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `7`, pre-tabulated. -/
def XLc0_0_5_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 1]]]

/-- Left route at the `c`-slot generator `7`, pre-tabulated. -/
def YLc0_0_5_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 1]]]

noncomputable def Xcc0_0_5_7 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_5_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_5_7 : (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_5_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 8 = 8` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_5_7 : ∀ I J g, Xc0_0_5_7 I J g = Xcc0_0_5_7 I J g := by
  decide +kernel

theorem hYtabc0_0_5_7 : ∀ I J g, Yc0_0_5_7 I J g = Ycc0_0_5_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `7`** (Koszul sign `+1`). -/
theorem hintc0_0_5_7 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T0_0_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_5 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Xc0_0_5_7 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 hfuseZ_0_5 hfuseZ_0_5 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Xcc0_0_5_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2)) (realRepBasis ((0 : ZMod 8) + 0 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_5_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Yc0_0_5_7 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hfuseZ_0_5 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 5)) Ycc0_0_5_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 5).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 5).2)) (realRepBasis ((0 : ZMod 8) + 0 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_5_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 5) (realGauge.gaugeSizeL 0 0 5).1 (realGauge.gaugeSizeL 0 0 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_5_7 TL0_0_5 YLc0_0_5_7 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint0_0_5 (i : Fin (realRepDim (0 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (0 : ZMod 8) i)) * T0_0_5
      = ((sgn (realRepBasisParity (0 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T0_0_5 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (0 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 1 := i.isLt
  have h0 : (i : ℕ) = 0 := by omega
  rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) from Fin.ext h0]
  exact hinta0_0_5_0

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint0_0_5 (i : Fin (realRepDim (0 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (0 : ZMod 8) i)) * T0_0_5
      = ((sgn (realRepBasisParity (0 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T0_0_5 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (0 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 1 := i.isLt
  have h0 : (i : ℕ) = 0 := by omega
  rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) from Fin.ext h0]
  exact hintb0_0_5_0

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint0_0_5 (i : Fin (realRepDim (5 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) i)) * T0_0_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T0_0_5 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h0]; exact hintc0_0_5_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h1]; exact hintc0_0_5_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h2]; exact hintc0_0_5_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h3]; exact hintc0_0_5_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h4]; exact hintc0_0_5_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h5]; exact hintc0_0_5_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h6]; exact hintc0_0_5_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h7]; exact hintc0_0_5_7

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT0_0_5_mem_gInterSpace :
    gtOfT ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 T0_0_5 ∈ gInterSpace ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 hT0_0_5 hAint0_0_5 hBint0_0_5 hCint0_0_5

theorem gtOfT0_0_5_ne_zero : gtOfT ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 T0_0_5 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) hsz0_0_5 T0_0_5_ne_zero

theorem gInterSpace0_0_5_ne_bot : gInterSpace ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT0_0_5_mem_gInterSpace, gtOfT0_0_5_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_0_0_5 : gParity ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (5 : ZMod 8) gInterSpace0_0_5_ne_bot).symm

end Triple_0_0_5

/-! ### The triple `(0,0,6)`

`gaugeSizeL = gaugeSizeR = (1,0)`, `dim D_6 = 4`, certgen parity `0`; the unit-slot shortcut: the connector is the identity, so every certificate carries the sign `+1`. -/
section Triple_0_0_6
open Module
theorem hsz0_0_6 : realGauge.gaugeSizeR 0 0 6 = realGauge.gaugeSizeL 0 0 6 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`1 x 1 x 4`). -/
def TL0_0_6 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0]]]

/-- The same literal read at the composite frame `Fin 1 ⊕ Fin 0`. -/
noncomputable def Tc0_0_6 : (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 6).val) → ℤ :=
  fun r s g => coeffGet TL0_0_6 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_6`. -/
noncomputable def T0_0_6 : ((realGauge.D ((0 : ZMod 8) + 0 + 6)).matrixSuper
    (realGauge.gaugeSizeL 0 0 6).1 (realGauge.gaugeSizeL 0 0 6).2).carrier :=
  matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 6)) Tc0_0_6

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT0_0_6 : T0_0_6 ∈ ((realGauge.D ((0 : ZMod 8) + 0 + 6)).matrixSuper
    (realGauge.gaugeSizeL 0 0 6).1 (realGauge.gaugeSizeL 0 0 6).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((0 : ZMod 8) + 0 + 6) Tc0_0_6 0 (by decide)

theorem T0_0_6_ne_zero : T0_0_6 ≠ 0 :=
  matOfCoeff_ne_zero ((0 : ZMod 8) + 0 + 6) Tc0_0_6 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa0_0_6_0 : (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 6).val) → ℤ :=
  fun I J g => if (ro (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 I) = (ro (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (6 : ZMod 8)).1 (realSize (0 : ZMod 8) (6 : ZMod 8)).2 (ro (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 I)
          * realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_6 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 6) (ri (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 I) (ri (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya0_0_6_0 : (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_0 (fuseRow (0 : ZMod 8) (0 : ZMod 8) (lo (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) I) (lo (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (0 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_0_6 (fuseRow ((0 : ZMod 8) + 0) (6 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa0_0_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa0_0_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0]]]

noncomputable def Xca0_0_6_0 : (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa0_0_6_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca0_0_6_0 : (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa0_0_6_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 4 = 4` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba0_0_6_0 : ∀ I J g, Xa0_0_6_0 I J g = Xca0_0_6_0 I J g := by
  decide +kernel

theorem hYtaba0_0_6_0 : ∀ I J g, Ya0_0_6_0 I J g = Yca0_0_6_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta0_0_6_0 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))) * T0_0_6
      = ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_6 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 6)) Xa0_0_6_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 hfuseZ_0_6 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 6)) Xca0_0_6_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2)) (realRepBasis ((0 : ZMod 8) + 0 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba0_0_6_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 6)) Ya0_0_6_0 := Matrix.ext fun I J => routeL_aSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hfuseZ_0_0 hfuseZ_0_6 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 6)) Yca0_0_6_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2)) (realRepBasis ((0 : ZMod 8) + 0 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba0_0_6_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 6) (realGauge.gaugeSizeL 0 0 6).1 (realGauge.gaugeSizeL 0 0 6).2 ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa0_0_6_0 TL0_0_6 YLa0_0_6_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb0_0_6_0 : (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_6 (fuseRow (0 : ZMod 8) (6 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 I) (ro (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 J) ee) (fuseCol (0 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_0_6 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 6) (ri (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 I) (ri (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb0_0_6_0 : (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_0 (fuseRow (0 : ZMod 8) (0 : ZMod 8) (lo (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) I) (lo (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (0 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_0_6 (fuseRow ((0 : ZMod 8) + 0) (6 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb0_0_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb0_0_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0]]]

noncomputable def Xcb0_0_6_0 : (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb0_0_6_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb0_0_6_0 : (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb0_0_6_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 4 = 4` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb0_0_6_0 : ∀ I J g, Xb0_0_6_0 I J g = Xcb0_0_6_0 I J g := by
  decide +kernel

theorem hYtabb0_0_6_0 : ∀ I J g, Yb0_0_6_0 I J g = Ycb0_0_6_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb0_0_6_0 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))) * T0_0_6
      = ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_6 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 6)) Xb0_0_6_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 hfuseZ_0_6 hfuseZ_0_6 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 6)) Xcb0_0_6_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2)) (realRepBasis ((0 : ZMod 8) + 0 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb0_0_6_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 6)) Yb0_0_6_0 := Matrix.ext fun I J => routeL_bSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hfuseZ_0_0 hfuseZ_0_6 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 6)) Ycb0_0_6_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2)) (realRepBasis ((0 : ZMod 8) + 0 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb0_0_6_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 6) (realGauge.gaugeSizeL 0 0 6).1 (realGauge.gaugeSizeL 0 0 6).2 ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb0_0_6_0 TL0_0_6 YLb0_0_6_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc0_0_6_0 : (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_6 (fuseRow (0 : ZMod 8) (6 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 I) (ro (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 J) ee) (fuseCol (0 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_0_6 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 6) (ri (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 I) (ri (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc0_0_6_0 : (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 6).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_6 (fuseRow ((0 : ZMod 8) + 0) (6 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc0_0_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc0_0_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0]]]

noncomputable def Xcc0_0_6_0 : (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_6_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_6_0 : (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_6_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 4 = 4` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_6_0 : ∀ I J g, Xc0_0_6_0 I J g = Xcc0_0_6_0 I J g := by
  decide +kernel

theorem hYtabc0_0_6_0 : ∀ I J g, Yc0_0_6_0 I J g = Ycc0_0_6_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc0_0_6_0 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T0_0_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_6 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 6)) Xc0_0_6_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 hfuseZ_0_6 hfuseZ_0_6 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 6)) Xcc0_0_6_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2)) (realRepBasis ((0 : ZMod 8) + 0 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_6_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 6)) Yc0_0_6_0 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hfuseZ_0_6 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 6)) Ycc0_0_6_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2)) (realRepBasis ((0 : ZMod 8) + 0 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_6_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 6) (realGauge.gaugeSizeL 0 0 6).1 (realGauge.gaugeSizeL 0 0 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_6_0 TL0_0_6 YLc0_0_6_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc0_0_6_1 : (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_6 (fuseRow (0 : ZMod 8) (6 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 I) (ro (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 J) ee) (fuseCol (0 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_0_6 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 6) (ri (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 I) (ri (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc0_0_6_1 : (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 6).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_6 (fuseRow ((0 : ZMod 8) + 0) (6 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc0_0_6_1 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc0_0_6_1 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0]]]

noncomputable def Xcc0_0_6_1 : (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_6_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_6_1 : (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_6_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 4 = 4` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_6_1 : ∀ I J g, Xc0_0_6_1 I J g = Xcc0_0_6_1 I J g := by
  decide +kernel

theorem hYtabc0_0_6_1 : ∀ I J g, Yc0_0_6_1 I J g = Ycc0_0_6_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc0_0_6_1 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T0_0_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_6 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 6)) Xc0_0_6_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 hfuseZ_0_6 hfuseZ_0_6 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 6)) Xcc0_0_6_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2)) (realRepBasis ((0 : ZMod 8) + 0 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_6_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 6)) Yc0_0_6_1 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hfuseZ_0_6 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 6)) Ycc0_0_6_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2)) (realRepBasis ((0 : ZMod 8) + 0 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_6_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 6) (realGauge.gaugeSizeL 0 0 6).1 (realGauge.gaugeSizeL 0 0 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_6_1 TL0_0_6 YLc0_0_6_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc0_0_6_2 : (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_6 (fuseRow (0 : ZMod 8) (6 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 I) (ro (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 J) ee) (fuseCol (0 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_0_6 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 6) (ri (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 I) (ri (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc0_0_6_2 : (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 6).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_6 (fuseRow ((0 : ZMod 8) + 0) (6 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc0_0_6_2 : List (List (List ℤ)) :=
  [[[0, 0, 1, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc0_0_6_2 : List (List (List ℤ)) :=
  [[[0, 0, 1, 0]]]

noncomputable def Xcc0_0_6_2 : (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_6_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_6_2 : (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_6_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 4 = 4` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_6_2 : ∀ I J g, Xc0_0_6_2 I J g = Xcc0_0_6_2 I J g := by
  decide +kernel

theorem hYtabc0_0_6_2 : ∀ I J g, Yc0_0_6_2 I J g = Ycc0_0_6_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc0_0_6_2 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T0_0_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_6 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 6)) Xc0_0_6_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 hfuseZ_0_6 hfuseZ_0_6 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 6)) Xcc0_0_6_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2)) (realRepBasis ((0 : ZMod 8) + 0 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_6_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 6)) Yc0_0_6_2 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hfuseZ_0_6 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 6)) Ycc0_0_6_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2)) (realRepBasis ((0 : ZMod 8) + 0 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_6_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 6) (realGauge.gaugeSizeL 0 0 6).1 (realGauge.gaugeSizeL 0 0 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_6_2 TL0_0_6 YLc0_0_6_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc0_0_6_3 : (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_6 (fuseRow (0 : ZMod 8) (6 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 I) (ro (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 J) ee) (fuseCol (0 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_0_6 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 6) (ri (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 I) (ri (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc0_0_6_3 : (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 6).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_6 (fuseRow ((0 : ZMod 8) + 0) (6 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc0_0_6_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc0_0_6_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1]]]

noncomputable def Xcc0_0_6_3 : (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_6_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_6_3 : (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_6_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 4 = 4` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_6_3 : ∀ I J g, Xc0_0_6_3 I J g = Xcc0_0_6_3 I J g := by
  decide +kernel

theorem hYtabc0_0_6_3 : ∀ I J g, Yc0_0_6_3 I J g = Ycc0_0_6_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc0_0_6_3 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T0_0_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_6 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 6)) Xc0_0_6_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 hfuseZ_0_6 hfuseZ_0_6 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 6)) Xcc0_0_6_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2)) (realRepBasis ((0 : ZMod 8) + 0 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_6_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 6)) Yc0_0_6_3 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hfuseZ_0_6 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 6)) Ycc0_0_6_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 6).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 6).2)) (realRepBasis ((0 : ZMod 8) + 0 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_6_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 6) (realGauge.gaugeSizeL 0 0 6).1 (realGauge.gaugeSizeL 0 0 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_6_3 TL0_0_6 YLc0_0_6_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint0_0_6 (i : Fin (realRepDim (0 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (0 : ZMod 8) i)) * T0_0_6
      = ((sgn (realRepBasisParity (0 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T0_0_6 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (0 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 1 := i.isLt
  have h0 : (i : ℕ) = 0 := by omega
  rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) from Fin.ext h0]
  exact hinta0_0_6_0

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint0_0_6 (i : Fin (realRepDim (0 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (0 : ZMod 8) i)) * T0_0_6
      = ((sgn (realRepBasisParity (0 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T0_0_6 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (0 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 1 := i.isLt
  have h0 : (i : ℕ) = 0 := by omega
  rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) from Fin.ext h0]
  exact hintb0_0_6_0

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint0_0_6 (i : Fin (realRepDim (6 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) i)) * T0_0_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T0_0_6 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h0]; exact hintc0_0_6_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h1]; exact hintc0_0_6_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h2]; exact hintc0_0_6_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h3]; exact hintc0_0_6_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT0_0_6_mem_gInterSpace :
    gtOfT ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 T0_0_6 ∈ gInterSpace ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 hT0_0_6 hAint0_0_6 hBint0_0_6 hCint0_0_6

theorem gtOfT0_0_6_ne_zero : gtOfT ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 T0_0_6 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) hsz0_0_6 T0_0_6_ne_zero

theorem gInterSpace0_0_6_ne_bot : gInterSpace ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT0_0_6_mem_gInterSpace, gtOfT0_0_6_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_0_0_6 : gParity ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (6 : ZMod 8) gInterSpace0_0_6_ne_bot).symm

end Triple_0_0_6

/-! ### The triple `(0,0,7)`

`gaugeSizeL = gaugeSizeR = (1,0)`, `dim D_7 = 2`, certgen parity `0`; the unit-slot shortcut: the connector is the identity, so every certificate carries the sign `+1`. -/
section Triple_0_0_7
open Module
theorem hsz0_0_7 : realGauge.gaugeSizeR 0 0 7 = realGauge.gaugeSizeL 0 0 7 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`1 x 1 x 2`). -/
def TL0_0_7 : List (List (List ℤ)) :=
  [[[1, 0]]]

/-- The same literal read at the composite frame `Fin 1 ⊕ Fin 0`. -/
noncomputable def Tc0_0_7 : (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 7).val) → ℤ :=
  fun r s g => coeffGet TL0_0_7 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_7`. -/
noncomputable def T0_0_7 : ((realGauge.D ((0 : ZMod 8) + 0 + 7)).matrixSuper
    (realGauge.gaugeSizeL 0 0 7).1 (realGauge.gaugeSizeL 0 0 7).2).carrier :=
  matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 7)) Tc0_0_7

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT0_0_7 : T0_0_7 ∈ ((realGauge.D ((0 : ZMod 8) + 0 + 7)).matrixSuper
    (realGauge.gaugeSizeL 0 0 7).1 (realGauge.gaugeSizeL 0 0 7).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((0 : ZMod 8) + 0 + 7) Tc0_0_7 0 (by decide)

theorem T0_0_7_ne_zero : T0_0_7 ≠ 0 :=
  matOfCoeff_ne_zero ((0 : ZMod 8) + 0 + 7) Tc0_0_7 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa0_0_7_0 : (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 7).val) → ℤ :=
  fun I J g => if (ro (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hsz0_0_7 I) = (ro (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hsz0_0_7 J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (7 : ZMod 8)).1 (realSize (0 : ZMod 8) (7 : ZMod 8)).2 (ro (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hsz0_0_7 I)
          * realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_7 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 7) (ri (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hsz0_0_7 I) (ri (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hsz0_0_7 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya0_0_7_0 : (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_0 (fuseRow (0 : ZMod 8) (0 : ZMod 8) (lo (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) I) (lo (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (0 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_0_7 (fuseRow ((0 : ZMod 8) + 0) (7 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa0_0_7_0 : List (List (List ℤ)) :=
  [[[1, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa0_0_7_0 : List (List (List ℤ)) :=
  [[[1, 0]]]

noncomputable def Xca0_0_7_0 : (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa0_0_7_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca0_0_7_0 : (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa0_0_7_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 2 = 2` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba0_0_7_0 : ∀ I J g, Xa0_0_7_0 I J g = Xca0_0_7_0 I J g := by
  decide +kernel

theorem hYtaba0_0_7_0 : ∀ I J g, Ya0_0_7_0 I J g = Yca0_0_7_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta0_0_7_0 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))) * T0_0_7
      = ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_7 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 7)) Xa0_0_7_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hsz0_0_7 hfuseZ_0_7 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 7)) Xca0_0_7_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2)) (realRepBasis ((0 : ZMod 8) + 0 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba0_0_7_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 7)) Ya0_0_7_0 := Matrix.ext fun I J => routeL_aSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hfuseZ_0_0 hfuseZ_0_7 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 7)) Yca0_0_7_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2)) (realRepBasis ((0 : ZMod 8) + 0 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba0_0_7_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 7) (realGauge.gaugeSizeL 0 0 7).1 (realGauge.gaugeSizeL 0 0 7).2 ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa0_0_7_0 TL0_0_7 YLa0_0_7_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb0_0_7_0 : (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_7 (fuseRow (0 : ZMod 8) (7 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hsz0_0_7 I) (ro (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hsz0_0_7 J) ee) (fuseCol (0 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_0_7 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 7) (ri (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hsz0_0_7 I) (ri (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hsz0_0_7 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb0_0_7_0 : (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_0 (fuseRow (0 : ZMod 8) (0 : ZMod 8) (lo (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) I) (lo (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (0 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_0_7 (fuseRow ((0 : ZMod 8) + 0) (7 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb0_0_7_0 : List (List (List ℤ)) :=
  [[[1, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb0_0_7_0 : List (List (List ℤ)) :=
  [[[1, 0]]]

noncomputable def Xcb0_0_7_0 : (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb0_0_7_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb0_0_7_0 : (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb0_0_7_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 2 = 2` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb0_0_7_0 : ∀ I J g, Xb0_0_7_0 I J g = Xcb0_0_7_0 I J g := by
  decide +kernel

theorem hYtabb0_0_7_0 : ∀ I J g, Yb0_0_7_0 I J g = Ycb0_0_7_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb0_0_7_0 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))) * T0_0_7
      = ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_7 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 7)) Xb0_0_7_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hsz0_0_7 hfuseZ_0_7 hfuseZ_0_7 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 7)) Xcb0_0_7_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2)) (realRepBasis ((0 : ZMod 8) + 0 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb0_0_7_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 7)) Yb0_0_7_0 := Matrix.ext fun I J => routeL_bSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hfuseZ_0_0 hfuseZ_0_7 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 7)) Ycb0_0_7_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2)) (realRepBasis ((0 : ZMod 8) + 0 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb0_0_7_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 7) (realGauge.gaugeSizeL 0 0 7).1 (realGauge.gaugeSizeL 0 0 7).2 ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb0_0_7_0 TL0_0_7 YLb0_0_7_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc0_0_7_0 : (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_7 (fuseRow (0 : ZMod 8) (7 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hsz0_0_7 I) (ro (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hsz0_0_7 J) ee) (fuseCol (0 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_0_7 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 7) (ri (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hsz0_0_7 I) (ri (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hsz0_0_7 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc0_0_7_0 : (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 7).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) I)
          * realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_7 (fuseRow ((0 : ZMod 8) + 0) (7 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc0_0_7_0 : List (List (List ℤ)) :=
  [[[1, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc0_0_7_0 : List (List (List ℤ)) :=
  [[[1, 0]]]

noncomputable def Xcc0_0_7_0 : (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 7).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_7_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_7_0 : (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 7).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_7_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 2 = 2` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_7_0 : ∀ I J g, Xc0_0_7_0 I J g = Xcc0_0_7_0 I J g := by
  decide +kernel

theorem hYtabc0_0_7_0 : ∀ I J g, Yc0_0_7_0 I J g = Ycc0_0_7_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc0_0_7_0 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T0_0_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_7 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 7)) Xc0_0_7_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hsz0_0_7 hfuseZ_0_7 hfuseZ_0_7 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 7)) Xcc0_0_7_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2)) (realRepBasis ((0 : ZMod 8) + 0 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_7_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 7)) Yc0_0_7_0 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hfuseZ_0_7 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 7)) Ycc0_0_7_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2)) (realRepBasis ((0 : ZMod 8) + 0 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_7_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 7) (realGauge.gaugeSizeL 0 0 7).1 (realGauge.gaugeSizeL 0 0 7).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_7_0 TL0_0_7 YLc0_0_7_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc0_0_7_1 : (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_0_7 (fuseRow (0 : ZMod 8) (7 : ZMod 8) (ro (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hsz0_0_7 I) (ro (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hsz0_0_7 J) ee) (fuseCol (0 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_0_7 (fuseRow (0 : ZMod 8) ((0 : ZMod 8) + 7) (ri (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hsz0_0_7 I) (ri (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hsz0_0_7 J) g) (fuseCol (0 : ZMod 8) ((0 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc0_0_7_1 : (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 7).val) → ℤ :=
  fun I J g => if (lo (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) I) = (lo (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) J) then
      ((sgn (sumParity (realSize (0 : ZMod 8) (0 : ZMod 8)).1 (realSize (0 : ZMod 8) (0 : ZMod 8)).2 (lo (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) I)
          * realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_0_7 (fuseRow ((0 : ZMod 8) + 0) (7 : ZMod 8) (li (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) I) (li (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((0 : ZMod 8) + 0) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc0_0_7_1 : List (List (List ℤ)) :=
  [[[0, 1]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc0_0_7_1 : List (List (List ℤ)) :=
  [[[0, 1]]]

noncomputable def Xcc0_0_7_1 : (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 7).val) → ℤ :=
  fun r s g => coeffGet XLc0_0_7_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc0_0_7_1 : (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2) → Fin (realRepDim ((0 : ZMod 8) + 0 + 7).val) → ℤ :=
  fun r s g => coeffGet YLc0_0_7_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 2 = 2` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc0_0_7_1 : ∀ I J g, Xc0_0_7_1 I J g = Xcc0_0_7_1 I J g := by
  decide +kernel

theorem hYtabc0_0_7_1 : ∀ I J g, Yc0_0_7_1 I J g = Ycc0_0_7_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc0_0_7_1 :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T0_0_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T0_0_7 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 7)) Xc0_0_7_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hsz0_0_7 hfuseZ_0_7 hfuseZ_0_7 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 7)) Xcc0_0_7_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2)) (realRepBasis ((0 : ZMod 8) + 0 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabc0_0_7_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 7)) Yc0_0_7_1 := Matrix.ext fun I J => routeL_cSlot_coeff (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hfuseZ_0_7 (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((0 : ZMod 8) + 0 + 7)) Ycc0_0_7_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 0 0 7).1 ⊕ Fin (realGauge.gaugeSizeL 0 0 7).2)) (realRepBasis ((0 : ZMod 8) + 0 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabc0_0_7_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((0 : ZMod 8) + 0 + 7) (realGauge.gaugeSizeL 0 0 7).1 (realGauge.gaugeSizeL 0 0 7).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc0_0_7_1 TL0_0_7 YLc0_0_7_1 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint0_0_7 (i : Fin (realRepDim (0 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (0 : ZMod 8) i)) * T0_0_7
      = ((sgn (realRepBasisParity (0 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T0_0_7 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (0 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 1 := i.isLt
  have h0 : (i : ℕ) = 0 := by omega
  rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) from Fin.ext h0]
  exact hinta0_0_7_0

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint0_0_7 (i : Fin (realRepDim (0 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (0 : ZMod 8) i)) * T0_0_7
      = ((sgn (realRepBasisParity (0 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T0_0_7 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (0 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 1 := i.isLt
  have h0 : (i : ℕ) = 0 := by omega
  rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) from Fin.ext h0]
  exact hintb0_0_7_0

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint0_0_7 (i : Fin (realRepDim (7 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) i)) * T0_0_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T0_0_7 * (realGauge.gaugeRouteL (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h0]; exact hintc0_0_7_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h1]; exact hintc0_0_7_1

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT0_0_7_mem_gInterSpace :
    gtOfT ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hsz0_0_7 T0_0_7 ∈ gInterSpace ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hsz0_0_7 hT0_0_7 hAint0_0_7 hBint0_0_7 hCint0_0_7

theorem gtOfT0_0_7_ne_zero : gtOfT ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hsz0_0_7 T0_0_7 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) hsz0_0_7 T0_0_7_ne_zero

theorem gInterSpace0_0_7_ne_bot : gInterSpace ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT0_0_7_mem_gInterSpace, gtOfT0_0_7_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_0_0_7 : gParity ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (0 : ZMod 8) (0 : ZMod 8) (7 : ZMod 8) gInterSpace0_0_7_ne_bot).symm

end Triple_0_0_7

end BatchEasy
end TripleCerts
end GaugeChi
end Superfusion

/-! ### Kernel self-check -/

#print axioms Superfusion.GaugeChi.TripleCerts.BatchEasy.gParity_0_0_0
#print axioms Superfusion.GaugeChi.TripleCerts.BatchEasy.gParity_0_0_1
#print axioms Superfusion.GaugeChi.TripleCerts.BatchEasy.gParity_0_0_2
#print axioms Superfusion.GaugeChi.TripleCerts.BatchEasy.gParity_0_0_3
#print axioms Superfusion.GaugeChi.TripleCerts.BatchEasy.gParity_0_0_4
#print axioms Superfusion.GaugeChi.TripleCerts.BatchEasy.gParity_0_0_5
#print axioms Superfusion.GaugeChi.TripleCerts.BatchEasy.gParity_0_0_6
#print axioms Superfusion.GaugeChi.TripleCerts.BatchEasy.gParity_0_0_7
