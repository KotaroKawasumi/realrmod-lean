/-
Copyright (c) 2026 Superfusion contributors.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Superfusion.Gauge.RealFuseSpecPeel2
import Superfusion.Gauge.RealFuseSpecTranspose
import Batteries.Tactic.OpenPrivate

/-!
# The `(3,5)` triple peel, and the `!![…]`-to-decoder bridges

This file closes the one branch that `Superfusion.Gauge.RealFuseSpecPeel2`
proved the mathematics of but did not ship, and converts two of its
neighbours into the shape the transpose file consumes.

## What is here

* `realFuseMatrix_3_5` — the `64 × 64` **deliverable** for the triple
  peel `peelFuse (peelFuse hypFuse)`, in the packed base-3 shape
  (`fuseRows_3_5` / `fuseLit_3_5`, copied verbatim from
  `scripts/certgen/out/lean_literals/fuse_3_5.txt`).
* `bridge_3_5`, `bridge_2_5`, `bridge_3_6` — the same three forward
  matrices in the *decoder* shape `∀ i j, realFuseMatrix a b i j =
  fuseLitFwd_a_b i j` that `Superfusion.Gauge.RealFuseSpecTranspose`
  takes as its hypothesis.
* `realFuseMatrix_5_3`, `realFuseMatrix_5_2`, `realFuseMatrix_6_3` —
  the three transposes, now unconditional.

## How the `64 × 64` closing step is done

`RealFuseSpecPeel2.hcol_3_5` is the complete, kernel-checked 64-column
expansion of `peelFuse (peelFuse hypFuse)`; it is `private`, so it is
brought into scope here with Batteries' `open private` (this adds no
axiom and no `sorry`; `#print axioms realFuseMatrix_3_5` reports only
`propext`, `Classical.choice`, `Quot.sound`).

The previous wave's closing step,
`refine Matrix.ext fun i j => ?_; …; fin_cases i <;> fin_cases j <;>
norm_num`, does not terminate at `N = 64`: it is `4096` *tactic* goals,
each re-evaluating sixteen length-`64` `![…]` literals.  The route taken
here has **no** `N²` tactic goal at all:

1. `entry35` — one declaration, generic in `i` and `j`, turns
   `realFuseMatrix 3 5 i j` into the eight-term sum
   `∑ₖ vₖ j * (if nₖ j = i then 1 else 0)`.  Cost `O(1)`.
2. `coefs` — one `fin_cases j` (64 goals, eight `rfl`s each) rewrites
   the eight real sign vectors `vₖ` as `fuseDecode ∘ kₖ` for base-3
   *code* vectors `kₖ : Fin 64 → ℕ`.  Cost `O(N)`.
3. `master` — a single kernel `decide` over all `4096` points checks,
   in `ℕ`, both that at most one of the eight `if`s fires and that the
   surviving code is the base-3 digit of `fuseRows_3_5`.  Cost: one
   `decide`, a few seconds.
4. `dmul` / `dpick_add` — two generic `ℝ`-side transport lemmas move
   the sum across the `fuseDecode` decoder, again generically in
   `i`, `j`.  Cost `O(1)`.

The disjointness that makes step 3 true is structural: the eight index
vectors of `hcol_3_5` take values in the eight disjoint blocks
`0–7, 8–15, …, 56–63`.
-/

namespace Superfusion

open Module TensorProduct GradedTensorProduct

open private hcol_3_5 baseBasis from Superfusion.Gauge.RealFuseSpecPeel2

set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! ### The packed literal (verbatim from the certificate generator) -/

/-- Packed row codes for `realFuseMatrix 3 5` (64 × 64).  Row `i` is
the base-3 numeral whose digit `j` (least-significant digit = column 0)
is the value code of entry `(i, j)`; codes: 0 ↦ 0, 1 ↦ 1, 2 ↦ -1. -/
def fuseRows_3_5 : Fin 64 → ℕ :=
  ![2289238852244456592879826979746,
    42410559250812678274900273932,
    9424564794587630444984852706,
    1570122993815617506342672492,
    763389748361581376155025724066,
    127179962499053901303651946572,
    28262208052401933867412809186,
    523587151244623860584766252,
    84801717530081437224643219908,
    2289180699553140846269690331106,
    1570203088515661776890746788,
    4714436097336032440628788386,
    127186450169757486934497390468,
    381869323884185263162350656226,
    1046934784322038819689734628,
    28261490117941245669035906466,
    4714436109499050974976999234,
    3140166221154666516007069812,
    2289180702507603639829836123394,
    42429942500532913730245642452,
    28261490154415477361618201154,
    523826450623908900010593972,
    381869324869406446708824796674,
    254353463913516870804081580692,
    3140245659340775990507420052,
    9424564806739942640464141806,
    84821100771696561809091562932,
    2289238849290293973339080215726,
    1047174083601215015332653012,
    28262208015930172868415650286,
    254359898406591738519834355572,
    763389749345901996973449526446,
    381869324869406449251852893028,
    254353463913516869956750101666,
    14131821924189585312082522092,
    1046934674853018143083156494,
    1144677575859306383817446119372,
    84801708663090762419123206734,
    4714436109499256960252803908,
    3140166221154597882157268706,
    254359898406591737672588615694,
    763389749345901994432745966148,
    523587041875666274176191906,
    14131104062674889868044003532,
    42410550391927113775418213346,
    1144619429076616050308976828652,
    3140245659340707363602489934,
    9424564806739736843475757668,
    14131104026204364153077293308,
    1047173974232257428914508354,
    763389748361581378695729297492,
    127179962499053900456406561006,
    9424564794587836241974300212,
    1570122993815548879466441646,
    1144619426122453446018650193628,
    84821091912810997309609384194,
    523826341154888223394454274,
    14131821960665052414219503892,
    127186450169757486087165557166,
    381869323884185260619322572988,
    1570203088515593143012249326,
    4714436097335826455354046108,
    42429933633542238924725511234,
    1144677578813769192629561722612]

/-- Packed literal for `realFuseMatrix 3 5`: decode digit `j` of
`fuseRows_3_5 i`. -/
def fuseLit_3_5 : Matrix (Fin 64) (Fin 64) ℝ :=
  Matrix.of fun i j =>
    match fuseRows_3_5 i / 3 ^ (j : ℕ) % 3 with
    | 1 => (1 : ℝ)
    | 2 => -1
    | _ => 0


/-! ### The eight columns of `hcol_3_5`, as data

`vv1 … vv8` are the real sign vectors of `hcol_3_5` verbatim; `kv1 …
kv8` are the same vectors as base-3 value codes (`1 ↦ 1`, `2 ↦ -1`);
`nv1 … nv8` are its eight target-frame index vectors. -/

private def vv1 : Fin 64 → ℝ :=
  ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, -1, 1, -1, 1,
    -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1,
    1, -1, -1, 1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1]

private def vv2 : Fin 64 → ℝ :=
  ![1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, -1, -1, 1, 1, -1,
    -1, 1, 1, 1, 1, -1, -1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1, -1,
    1]

private def vv3 : Fin 64 → ℝ :=
  ![1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, -1, -1, -1, -1,
    -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, 1, 1, -1, -1, -1,
    -1, 1, 1, -1, -1, 1, 1, -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1, 1, -1,
    -1, 1]

private def vv4 : Fin 64 → ℝ :=
  ![1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1, -1, 1, 1,
    -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1,
    -1, 1, -1, 1, -1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1]

private def vv5 : Fin 64 → ℝ :=
  ![1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, 1, -1, 1, -1, 1,
    -1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1,
    1, -1, -1, 1, 1, -1, 1, 1, -1, -1, 1, 1, -1, -1, -1, -1, 1, 1, -1, -1, 1,
    1]

private def vv6 : Fin 64 → ℝ :=
  ![1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1, -1, 1, 1, -1,
    -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1,
    -1, 1, -1]

private def vv7 : Fin 64 → ℝ :=
  ![1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1, -1,
    -1, 1, 1, -1, -1, 1, 1, -1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1,
    -1, 1, 1, -1]

private def vv8 : Fin 64 → ℝ :=
  ![1, 1, -1, -1, 1, 1, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1, 1, -1, -1, 1, 1,
    -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, 1, -1,
    1, -1, 1, -1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1,
    1]

private def kv1 : Fin 64 → ℕ :=
  ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1,
    2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1,
    2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2]

private def kv2 : Fin 64 → ℕ :=
  ![1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 1,
    1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2,
    1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1]

private def kv3 : Fin 64 → ℕ :=
  ![1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1,
    1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1]

private def kv4 : Fin 64 → ℕ :=
  ![1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 1, 1,
    2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]

private def kv5 : Fin 64 → ℕ :=
  ![1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2,
    1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1,
    2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 1, 1]

private def kv6 : Fin 64 → ℕ :=
  ![1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2,
    2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2,
    1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2]

private def kv7 : Fin 64 → ℕ :=
  ![1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1,
    1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2]

private def kv8 : Fin 64 → ℕ :=
  ![1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2,
    1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1]

private def nv1 : Fin 64 → Fin 64 :=
  ![0, 4, 5, 1, 6, 2, 3, 7, 4, 0, 1, 5, 2, 6, 7, 3, 5, 1, 0, 4, 3, 7, 6, 2, 1,
    5, 4, 0, 7, 3, 2, 6, 6, 2, 3, 7, 0, 4, 5, 1, 2, 6, 7, 3, 4, 0, 1, 5, 3, 7,
    6, 2, 5, 1, 0, 4, 7, 3, 2, 6, 1, 5, 4, 0]

private def nv2 : Fin 64 → Fin 64 :=
  ![54, 50, 51, 55, 48, 52, 53, 49, 50, 54, 55, 51, 52, 48, 49, 53, 51, 55,
    54, 50, 53, 49, 48, 52, 55, 51, 50, 54, 49, 53, 52, 48, 48, 52, 53, 49,
    54, 50, 51, 55, 52, 48, 49, 53, 50, 54, 55, 51, 53, 49, 48, 52, 51, 55,
    54, 50, 49, 53, 52, 48, 55, 51, 50, 54]

private def nv3 : Fin 64 → Fin 64 :=
  ![45, 41, 40, 44, 43, 47, 46, 42, 41, 45, 44, 40, 47, 43, 42, 46, 40, 44,
    45, 41, 46, 42, 43, 47, 44, 40, 41, 45, 42, 46, 47, 43, 43, 47, 46, 42,
    45, 41, 40, 44, 47, 43, 42, 46, 41, 45, 44, 40, 46, 42, 43, 47, 40, 44,
    45, 41, 42, 46, 47, 43, 44, 40, 41, 45]

private def nv4 : Fin 64 → Fin 64 :=
  ![27, 31, 30, 26, 29, 25, 24, 28, 31, 27, 26, 30, 25, 29, 28, 24, 30, 26,
    27, 31, 24, 28, 29, 25, 26, 30, 31, 27, 28, 24, 25, 29, 29, 25, 24, 28,
    27, 31, 30, 26, 25, 29, 28, 24, 31, 27, 26, 30, 24, 28, 29, 25, 30, 26,
    27, 31, 28, 24, 25, 29, 26, 30, 31, 27]

private def nv5 : Fin 64 → Fin 64 :=
  ![36, 32, 33, 37, 34, 38, 39, 35, 32, 36, 37, 33, 38, 34, 35, 39, 33, 37,
    36, 32, 39, 35, 34, 38, 37, 33, 32, 36, 35, 39, 38, 34, 34, 38, 39, 35,
    36, 32, 33, 37, 38, 34, 35, 39, 32, 36, 37, 33, 39, 35, 34, 38, 33, 37,
    36, 32, 35, 39, 38, 34, 37, 33, 32, 36]

private def nv6 : Fin 64 → Fin 64 :=
  ![18, 22, 23, 19, 20, 16, 17, 21, 22, 18, 19, 23, 16, 20, 21, 17, 23, 19,
    18, 22, 17, 21, 20, 16, 19, 23, 22, 18, 21, 17, 16, 20, 20, 16, 17, 21,
    18, 22, 23, 19, 16, 20, 21, 17, 22, 18, 19, 23, 17, 21, 20, 16, 23, 19,
    18, 22, 21, 17, 16, 20, 19, 23, 22, 18]

private def nv7 : Fin 64 → Fin 64 :=
  ![9, 13, 12, 8, 15, 11, 10, 14, 13, 9, 8, 12, 11, 15, 14, 10, 12, 8, 9, 13,
    10, 14, 15, 11, 8, 12, 13, 9, 14, 10, 11, 15, 15, 11, 10, 14, 9, 13, 12,
    8, 11, 15, 14, 10, 13, 9, 8, 12, 10, 14, 15, 11, 12, 8, 9, 13, 14, 10, 11,
    15, 8, 12, 13, 9]

private def nv8 : Fin 64 → Fin 64 :=
  ![63, 59, 58, 62, 57, 61, 60, 56, 59, 63, 62, 58, 61, 57, 56, 60, 58, 62,
    63, 59, 60, 56, 57, 61, 62, 58, 59, 63, 56, 60, 61, 57, 57, 61, 60, 56,
    63, 59, 58, 62, 61, 57, 56, 60, 59, 63, 62, 58, 60, 56, 57, 61, 58, 62,
    63, 59, 56, 60, 61, 57, 62, 58, 59, 63]

/-! ### The decoder-side transport lemmas -/

private theorem fuseDecode_zero : fuseDecode 0 = 0 := rfl

/-- Selecting with a real `0/1` indicator is selecting the code. -/
private theorem dmul (c : ℕ) (P : Prop) [Decidable P] :
    fuseDecode c * (if P then (1 : ℝ) else 0)
      = fuseDecode (if P then c else 0) := by
  by_cases h : P
  · rw [if_pos h, if_pos h, mul_one]
  · rw [if_neg h, if_neg h, mul_zero, fuseDecode_zero]

/-- Left-biased merge of two value codes. -/
private def dpick (a b : ℕ) : ℕ := if a = 0 then b else a

/-- Adding two decoded codes, one of which is `0`, is decoding their
merge.  This is the only place where "at most one column hits row `i`"
is used, and it is supplied point-by-point by `master`. -/
private theorem dpick_add (a b : ℕ) (h : a = 0 ∨ b = 0) :
    fuseDecode a + fuseDecode b = fuseDecode (dpick a b) := by
  unfold dpick
  rcases h with h | h
  · subst h; rw [if_pos rfl, fuseDecode_zero, zero_add]
  · subst h
    rw [fuseDecode_zero, add_zero]
    by_cases ha : a = 0
    · rw [if_pos ha, ha]
    · rw [if_neg ha]

/-! ### The `4096`-point kernel certificate -/


private def tt1 (i j : Fin 64) : ℕ := if nv1 j = i then kv1 j else 0

private def tt2 (i j : Fin 64) : ℕ := if nv2 j = i then kv2 j else 0

private def tt3 (i j : Fin 64) : ℕ := if nv3 j = i then kv3 j else 0

private def tt4 (i j : Fin 64) : ℕ := if nv4 j = i then kv4 j else 0

private def tt5 (i j : Fin 64) : ℕ := if nv5 j = i then kv5 j else 0

private def tt6 (i j : Fin 64) : ℕ := if nv6 j = i then kv6 j else 0

private def tt7 (i j : Fin 64) : ℕ := if nv7 j = i then kv7 j else 0

private def tt8 (i j : Fin 64) : ℕ := if nv8 j = i then kv8 j else 0


/-- **The table certificate.**  For every one of the `64 × 64` points:
the first seven conjuncts say that merging the eight column
contributions left-to-right never merges two nonzero codes (i.e. at
most one of the eight `hcol_3_5` columns lands on row `i`), and the
last says that the surviving code is exactly the base-3 digit `j` of
`fuseRows_3_5 i`.  Checked by the kernel. -/
private theorem master : ∀ i j : Fin 64,
    (tt1 i j = 0 ∨ tt2 i j = 0)
  ∧ (dpick (tt1 i j) (tt2 i j) = 0
      ∨ tt3 i j = 0)
  ∧ (dpick (dpick (tt1 i j) (tt2 i j)) (tt3 i j) = 0
      ∨ tt4 i j = 0)
  ∧ (dpick (dpick (dpick (tt1 i j) (tt2 i j)) (tt3 i j)) (tt4 i j) = 0
      ∨ tt5 i j = 0)
  ∧ (dpick (dpick (dpick (dpick (tt1 i j) (tt2 i j)) (tt3 i j)) (tt4 i j)) (tt5 i j) = 0
      ∨ tt6 i j = 0)
  ∧ (dpick (dpick (dpick (dpick (dpick (tt1 i j) (tt2 i j)) (tt3 i j)) (tt4 i j)) (tt5 i j)) (tt6 i j) = 0
      ∨ tt7 i j = 0)
  ∧ (dpick (dpick (dpick (dpick (dpick (dpick (tt1 i j) (tt2 i j)) (tt3 i j)) (tt4 i j)) (tt5 i j)) (tt6 i j)) (tt7 i j) = 0
      ∨ tt8 i j = 0)
  ∧ dpick (dpick (dpick (dpick (dpick (dpick (dpick (tt1 i j) (tt2 i j)) (tt3 i j)) (tt4 i j)) (tt5 i j)) (tt6 i j)) (tt7 i j)) (tt8 i j)
      = fuseRows_3_5 i / 3 ^ (j : ℕ) % 3 := by decide


/-! ### From `hcol_3_5` to a single matrix entry -/

/-- The entry formula, generic in `i` and `j`: no case split, one
`LinearMap.toMatrix` unfolding and one instance of `hcol_3_5`. -/
private theorem entry35raw (i j : Fin 64) :
    realFuseMatrix 3 5 i j
      =
      (![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1] j : ℝ)
          * (if (![0, 4, 5, 1, 6, 2, 3, 7, 4, 0, 1, 5, 2, 6, 7, 3, 5, 1, 0, 4, 3, 7, 6, 2, 1, 5, 4, 0, 7, 3, 2, 6, 6, 2, 3, 7, 0, 4, 5, 1, 2, 6, 7, 3, 4, 0, 1, 5, 3, 7, 6, 2, 5, 1, 0, 4, 7, 3, 2, 6, 1, 5, 4, 0] j : Fin 64) = i then 1 else 0)
      +
      (![1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, -1, -1, 1, 1, -1, -1, 1, 1, 1, 1, -1, -1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1] j : ℝ)
          * (if (![54, 50, 51, 55, 48, 52, 53, 49, 50, 54, 55, 51, 52, 48, 49, 53, 51, 55, 54, 50, 53, 49, 48, 52, 55, 51, 50, 54, 49, 53, 52, 48, 48, 52, 53, 49, 54, 50, 51, 55, 52, 48, 49, 53, 50, 54, 55, 51, 53, 49, 48, 52, 51, 55, 54, 50, 49, 53, 52, 48, 55, 51, 50, 54] j : Fin 64) = i then 1 else 0)
      +
      (![1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, 1, 1, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1, -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1] j : ℝ)
          * (if (![45, 41, 40, 44, 43, 47, 46, 42, 41, 45, 44, 40, 47, 43, 42, 46, 40, 44, 45, 41, 46, 42, 43, 47, 44, 40, 41, 45, 42, 46, 47, 43, 43, 47, 46, 42, 45, 41, 40, 44, 47, 43, 42, 46, 41, 45, 44, 40, 46, 42, 43, 47, 40, 44, 45, 41, 42, 46, 47, 43, 44, 40, 41, 45] j : Fin 64) = i then 1 else 0)
      +
      (![1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1] j : ℝ)
          * (if (![27, 31, 30, 26, 29, 25, 24, 28, 31, 27, 26, 30, 25, 29, 28, 24, 30, 26, 27, 31, 24, 28, 29, 25, 26, 30, 31, 27, 28, 24, 25, 29, 29, 25, 24, 28, 27, 31, 30, 26, 25, 29, 28, 24, 31, 27, 26, 30, 24, 28, 29, 25, 30, 26, 27, 31, 28, 24, 25, 29, 26, 30, 31, 27] j : Fin 64) = i then 1 else 0)
      +
      (![1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, 1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, 1, 1, -1, -1, 1, 1, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1] j : ℝ)
          * (if (![36, 32, 33, 37, 34, 38, 39, 35, 32, 36, 37, 33, 38, 34, 35, 39, 33, 37, 36, 32, 39, 35, 34, 38, 37, 33, 32, 36, 35, 39, 38, 34, 34, 38, 39, 35, 36, 32, 33, 37, 38, 34, 35, 39, 32, 36, 37, 33, 39, 35, 34, 38, 33, 37, 36, 32, 35, 39, 38, 34, 37, 33, 32, 36] j : Fin 64) = i then 1 else 0)
      +
      (![1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1] j : ℝ)
          * (if (![18, 22, 23, 19, 20, 16, 17, 21, 22, 18, 19, 23, 16, 20, 21, 17, 23, 19, 18, 22, 17, 21, 20, 16, 19, 23, 22, 18, 21, 17, 16, 20, 20, 16, 17, 21, 18, 22, 23, 19, 16, 20, 21, 17, 22, 18, 19, 23, 17, 21, 20, 16, 23, 19, 18, 22, 21, 17, 16, 20, 19, 23, 22, 18] j : Fin 64) = i then 1 else 0)
      +
      (![1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1] j : ℝ)
          * (if (![9, 13, 12, 8, 15, 11, 10, 14, 13, 9, 8, 12, 11, 15, 14, 10, 12, 8, 9, 13, 10, 14, 15, 11, 8, 12, 13, 9, 14, 10, 11, 15, 15, 11, 10, 14, 9, 13, 12, 8, 11, 15, 14, 10, 13, 9, 8, 12, 10, 14, 15, 11, 12, 8, 9, 13, 14, 10, 11, 15, 8, 12, 13, 9] j : Fin 64) = i then 1 else 0)
      +
      (![1, 1, -1, -1, 1, 1, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, 1, -1, 1, -1, 1, -1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1] j : ℝ)
          * (if (![63, 59, 58, 62, 57, 61, 60, 56, 59, 63, 62, 58, 61, 57, 56, 60, 58, 62, 63, 59, 60, 56, 57, 61, 62, 58, 59, 63, 56, 60, 61, 57, 57, 61, 60, 56, 63, 59, 58, 62, 61, 57, 56, 60, 59, 63, 62, 58, 60, 56, 57, 61, 58, 62, 63, 59, 56, 60, 61, 57, 62, 58, 59, 63] j : Fin 64) = i then 1 else 0) := by
  show LinearMap.toMatrix
      (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
        (B := divisionTower (1 : ℝ) 3)
        (towerBasis (-1) 3) (towerBasis 1 3))
      (matrixSuperBasis (P := SuperAlgebra.base ℝ) baseBasis 4 4)
      ((peelFuse (peelFuse hypFuse)).toAlgEquiv.toLinearMap) i j = _
  rw [LinearMap.toMatrix_apply, AlgEquiv.toLinearMap_apply, hcol_3_5 j,
    map_add, map_add, map_add, map_add, map_add, map_add, map_add,
    map_smul, map_smul, map_smul, map_smul, map_smul, map_smul, map_smul,
    map_smul,
    Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply,
    Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply,
    Finsupp.add_apply,
    Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.smul_apply,
    Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.smul_apply,
    Finsupp.smul_apply, Finsupp.smul_apply,
    Basis.repr_self_apply, Basis.repr_self_apply, Basis.repr_self_apply,
    Basis.repr_self_apply, Basis.repr_self_apply, Basis.repr_self_apply,
    Basis.repr_self_apply, Basis.repr_self_apply,
    smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, smul_eq_mul, smul_eq_mul]


/-- The same, with the column data folded into `vv*` / `nv*`. -/
private theorem entry35 (i j : Fin 64) :
    realFuseMatrix 3 5 i j
      =
      vv1 j * (if nv1 j = i then 1 else 0)
      +
      vv2 j * (if nv2 j = i then 1 else 0)
      +
      vv3 j * (if nv3 j = i then 1 else 0)
      +
      vv4 j * (if nv4 j = i then 1 else 0)
      +
      vv5 j * (if nv5 j = i then 1 else 0)
      +
      vv6 j * (if nv6 j = i then 1 else 0)
      +
      vv7 j * (if nv7 j = i then 1 else 0)
      +
      vv8 j * (if nv8 j = i then 1 else 0) :=
  entry35raw i j


/-- The eight real sign vectors are the decodings of the eight code
vectors.  One `fin_cases` on `j`; eight definitional checks each. -/
private theorem coefs (j : Fin 64) :
    vv1 j = fuseDecode (kv1 j)
  ∧ vv2 j = fuseDecode (kv2 j)
  ∧ vv3 j = fuseDecode (kv3 j)
  ∧ vv4 j = fuseDecode (kv4 j)
  ∧ vv5 j = fuseDecode (kv5 j)
  ∧ vv6 j = fuseDecode (kv6 j)
  ∧ vv7 j = fuseDecode (kv7 j)
  ∧ vv8 j = fuseDecode (kv8 j) := by
  fin_cases j <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-! ### The deliverable -/

/-- **Deliverable `(3,5)`** (`64 × 64`, the triple peel
`peelFuse (peelFuse hypFuse)`): the fusion matrix is the packed
base-3 literal emitted by `scripts/certgen`. -/
theorem realFuseMatrix_3_5 : ∀ (i j : Fin 64),
    realFuseMatrix 3 5 i j = fuseLit_3_5 i j := by
  intro i j
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := master i j
  refine (entry35 i j).trans ?_
  rw [(coefs j).1, (coefs j).2.1, (coefs j).2.2.1, (coefs j).2.2.2.1, (coefs j).2.2.2.2.1, (coefs j).2.2.2.2.2.1, (coefs j).2.2.2.2.2.2.1, (coefs j).2.2.2.2.2.2.2,
    dmul, dmul, dmul, dmul, dmul, dmul, dmul, dmul]
  show fuseDecode (tt1 i j) + fuseDecode (tt2 i j) + fuseDecode (tt3 i j) + fuseDecode (tt4 i j) + fuseDecode (tt5 i j) + fuseDecode (tt6 i j) + fuseDecode (tt7 i j) + fuseDecode (tt8 i j) = _
  rw [dpick_add _ _ h1, dpick_add _ _ h2, dpick_add _ _ h3,
    dpick_add _ _ h4, dpick_add _ _ h5, dpick_add _ _ h6,
    dpick_add _ _ h7, h8]
  rfl

/-- **Decoder shape at `(3,5)`**, the hypothesis form consumed by
`realFuseMatrix_5_3_of_forward`. -/
theorem bridge_3_5 : ∀ (i j : Fin 64),
    realFuseMatrix 3 5 i j = fuseLitFwd_3_5 i j := by
  intro i j
  exact (realFuseMatrix_3_5 i j).trans rfl

/-- **Deliverable `(5,3)`**: the transpose, now unconditional. -/
theorem realFuseMatrix_5_3 : ∀ (i j : Fin 64),
    realFuseMatrix 5 3 i j = fuseLit_5_3 i j :=
  realFuseMatrix_5_3_of_forward bridge_3_5

/-! ### The two `!![…]`-to-decoder bridges

`RealFuseSpecPeel2` ships `(2,5)` and `(3,6)` as `!![…]` literals, while
`RealFuseSpecTranspose` states its hypotheses in decoder form.  These
two lemmas are the conversion, and they discharge
`realFuseMatrix_5_2_of_forward` and `realFuseMatrix_6_3_of_forward`. -/

/-- **Decoder shape at `(2,5)`**. -/
theorem bridge_2_5 : ∀ (i j : Fin 32),
    realFuseMatrix 2 5 i j = fuseLitFwd_2_5 i j := by
  intro i j
  rw [realFuseMatrix_2_5]
  fin_cases i <;> fin_cases j <;> rfl

/-- **Deliverable `(5,2)`**: the transpose, now unconditional. -/
theorem realFuseMatrix_5_2 : ∀ (i j : Fin 32),
    realFuseMatrix 5 2 i j = fuseLit_5_2 i j :=
  realFuseMatrix_5_2_of_forward bridge_2_5

/-- **Decoder shape at `(3,6)`**. -/
theorem bridge_3_6 : ∀ (i j : Fin 32),
    realFuseMatrix 3 6 i j = fuseLitFwd_3_6 i j := by
  intro i j
  rw [realFuseMatrix_3_6]
  fin_cases i <;> fin_cases j <;> rfl

/-- **Deliverable `(6,3)`**: the transpose, now unconditional. -/
theorem realFuseMatrix_6_3 : ∀ (i j : Fin 32),
    realFuseMatrix 6 3 i j = fuseLit_6_3 i j :=
  realFuseMatrix_6_3_of_forward bridge_3_6

end Superfusion
