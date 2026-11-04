/-
Superfusion / GaugeChi / TtabAPI

**THE UNIFORM INTERFACE, NOW TOTAL.**  Everything below `Ttab` is written once,
for every triple, with no case split of any kind: no `hsz`, no `by_cases`, no
`generic`/`exceptional`, no frame, no permutation, no matrix literal.

WHY THERE IS A SPLIT AT ALL, AND WHY IT STOPS HERE
--------------------------------------------------
The 512 triples of `realGauge` fall into two construction regimes:

* the **generic** 500, where `gaugeSizeR a b c = gaugeSizeL a b c`, so the two
  routes share one composite frame and the connector is a SQUARE matrix over
  `D_{a+b+c}` (`gtOfT`, `GaugeChi/RouteMatrixProto.lean`, instantiated by the
  generated `GaugeChi/TripleCerts/*.lean`);
* the **exceptional** 12 — the `(a,4,4)` and `(4,4,c)` with `a, c ≠ 0, 4` —
  where the two frames have different shapes and the connector is RECTANGULAR
  (`gtOfTNative`, `GaugeChi/RouteBridgeNative.lean`, instantiated by
  `GaugeChi/TripleCerts/Exceptional.lean`).

Those two constructions have genuinely different types.  The split is real,
and it is contained entirely inside the two blocks.  What crosses the boundary
into this file is a single proposition, identical in shape for all 512:

    gInterSpace ℝ realGauge a b c (pTable a b c) ≠ ⊥                 (`Covered`)

`Covered` mentions no frame, no size, no matrix and no route.  Both blocks
produce it; nothing downstream can tell which one did.  `Ttab` is then
extracted from it uniformly, and `gParity_eq_pTable` follows for every covered
triple by `gParity_unique` alone.

WHAT IS OPEN: NOTHING
---------------------
`IsCovered` — the whole rollout obligation — is PROVED (§6).  All 512 triples
are registered in §4, dispatched in §5, and the payoff is §7's

    gParity_eq_pTable_all (a b c : ZMod 8) :
      gParity ℝ realGauge a b c = pTable a b c

with NO hypothesis, at every one of the 512 triples.

Where the 512 certificates come from:

* 498 from the generated per-group modules `TripleCerts.G0_1` … `G7_5`;
* 12 from `TripleCerts.Exceptional` (the rectangular block);
*  2 — `(1,6,1)` and `(1,7,1)` — from `RouteBridgeProto`, where they were
   worked by hand as the pilot pair before the generator existed.  They are
   the only two triples with no generated certificate, and they are covered,
   not assumed.

No `sorry`, no `native_decide`, no new axioms.
-/
import Superfusion.GaugeChi.TripleCerts.BatchEasy
import Superfusion.GaugeChi.TripleCerts.BatchHeavy
import Superfusion.GaugeChi.TripleCerts.BatchMedium
import Superfusion.GaugeChi.TripleCerts.Exceptional
import Superfusion.GaugeChi.TripleCerts.FuseShadows
import Superfusion.GaugeChi.TripleCerts.G0_1
import Superfusion.GaugeChi.TripleCerts.G0_2
import Superfusion.GaugeChi.TripleCerts.G0_3
import Superfusion.GaugeChi.TripleCerts.G1_1
import Superfusion.GaugeChi.TripleCerts.G1_2
import Superfusion.GaugeChi.TripleCerts.G1_3
import Superfusion.GaugeChi.TripleCerts.G1_4
import Superfusion.GaugeChi.TripleCerts.G2_1
import Superfusion.GaugeChi.TripleCerts.G2_10
import Superfusion.GaugeChi.TripleCerts.G2_11
import Superfusion.GaugeChi.TripleCerts.G2_12
import Superfusion.GaugeChi.TripleCerts.G2_2
import Superfusion.GaugeChi.TripleCerts.G2_3
import Superfusion.GaugeChi.TripleCerts.G2_4
import Superfusion.GaugeChi.TripleCerts.G2_5
import Superfusion.GaugeChi.TripleCerts.G2_6
import Superfusion.GaugeChi.TripleCerts.G2_7
import Superfusion.GaugeChi.TripleCerts.G2_8
import Superfusion.GaugeChi.TripleCerts.G2_9
import Superfusion.GaugeChi.TripleCerts.G3_1
import Superfusion.GaugeChi.TripleCerts.G3_10
import Superfusion.GaugeChi.TripleCerts.G3_11
import Superfusion.GaugeChi.TripleCerts.G3_12
import Superfusion.GaugeChi.TripleCerts.G3_13
import Superfusion.GaugeChi.TripleCerts.G3_14
import Superfusion.GaugeChi.TripleCerts.G3_15
import Superfusion.GaugeChi.TripleCerts.G3_16
import Superfusion.GaugeChi.TripleCerts.G3_17
import Superfusion.GaugeChi.TripleCerts.G3_18
import Superfusion.GaugeChi.TripleCerts.G3_19
import Superfusion.GaugeChi.TripleCerts.G3_2
import Superfusion.GaugeChi.TripleCerts.G3_20
import Superfusion.GaugeChi.TripleCerts.G3_21
import Superfusion.GaugeChi.TripleCerts.G3_22
import Superfusion.GaugeChi.TripleCerts.G3_3
import Superfusion.GaugeChi.TripleCerts.G3_4
import Superfusion.GaugeChi.TripleCerts.G3_5
import Superfusion.GaugeChi.TripleCerts.G3_6
import Superfusion.GaugeChi.TripleCerts.G3_7
import Superfusion.GaugeChi.TripleCerts.G3_8
import Superfusion.GaugeChi.TripleCerts.G3_9
import Superfusion.GaugeChi.TripleCerts.G4_1
import Superfusion.GaugeChi.TripleCerts.G4_10
import Superfusion.GaugeChi.TripleCerts.G4_11
import Superfusion.GaugeChi.TripleCerts.G4_2
import Superfusion.GaugeChi.TripleCerts.G4_3
import Superfusion.GaugeChi.TripleCerts.G4_4
import Superfusion.GaugeChi.TripleCerts.G4_5
import Superfusion.GaugeChi.TripleCerts.G4_6
import Superfusion.GaugeChi.TripleCerts.G4_7
import Superfusion.GaugeChi.TripleCerts.G4_8
import Superfusion.GaugeChi.TripleCerts.G4_9
import Superfusion.GaugeChi.TripleCerts.G5_1
import Superfusion.GaugeChi.TripleCerts.G5_10
import Superfusion.GaugeChi.TripleCerts.G5_11
import Superfusion.GaugeChi.TripleCerts.G5_12
import Superfusion.GaugeChi.TripleCerts.G5_13
import Superfusion.GaugeChi.TripleCerts.G5_14
import Superfusion.GaugeChi.TripleCerts.G5_15
import Superfusion.GaugeChi.TripleCerts.G5_16
import Superfusion.GaugeChi.TripleCerts.G5_17
import Superfusion.GaugeChi.TripleCerts.G5_18
import Superfusion.GaugeChi.TripleCerts.G5_19
import Superfusion.GaugeChi.TripleCerts.G5_2
import Superfusion.GaugeChi.TripleCerts.G5_20
import Superfusion.GaugeChi.TripleCerts.G5_21
import Superfusion.GaugeChi.TripleCerts.G5_22
import Superfusion.GaugeChi.TripleCerts.G5_3
import Superfusion.GaugeChi.TripleCerts.G5_4
import Superfusion.GaugeChi.TripleCerts.G5_5
import Superfusion.GaugeChi.TripleCerts.G5_6
import Superfusion.GaugeChi.TripleCerts.G5_7
import Superfusion.GaugeChi.TripleCerts.G5_8
import Superfusion.GaugeChi.TripleCerts.G5_9
import Superfusion.GaugeChi.TripleCerts.G6_1
import Superfusion.GaugeChi.TripleCerts.G6_10
import Superfusion.GaugeChi.TripleCerts.G6_11
import Superfusion.GaugeChi.TripleCerts.G6_12
import Superfusion.GaugeChi.TripleCerts.G6_2
import Superfusion.GaugeChi.TripleCerts.G6_3
import Superfusion.GaugeChi.TripleCerts.G6_4
import Superfusion.GaugeChi.TripleCerts.G6_5
import Superfusion.GaugeChi.TripleCerts.G6_6
import Superfusion.GaugeChi.TripleCerts.G6_7
import Superfusion.GaugeChi.TripleCerts.G6_8
import Superfusion.GaugeChi.TripleCerts.G6_9
import Superfusion.GaugeChi.TripleCerts.G7_1
import Superfusion.GaugeChi.TripleCerts.G7_2
import Superfusion.GaugeChi.TripleCerts.G7_3
import Superfusion.GaugeChi.TripleCerts.G7_4
import Superfusion.GaugeChi.TripleCerts.G7_5
import Superfusion.GaugeChi.TripleCerts.Generic1
import Superfusion.GaugeChi.TripleCerts.Heavy88A
import Superfusion.GaugeChi.TripleCerts.Heavy88B

namespace Superfusion
namespace GaugeChi
namespace TtabAPI

/-! ## 1. The frozen parity table

`pTable a b c` is the certgen table `p`, all 512 entries, packed one `ZMod 8`
row per byte: `pCode[8a + b]` has bit `c` set exactly when the triple
`(a,b,c)` is odd.  172 of the 512 are odd.

This is DATA, frozen against `Data/certificates/real_lean_frame_transport.json`
(field `parity`, which the audit records as unchanged by the frame transport:
`p_new = p_old`).  It is not derived from anything in Lean; the content of
§3–§7 is exactly that the semantics agrees with it. -/

/-- The packed parity table: 64 bytes, `pCode[8a+b]` bit `c`. -/
def pCode : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0,
   0, 16, 10, 150, 102, 202, 186, 154,
   0, 18, 152, 242, 82, 240, 96, 186,
   0, 126, 124, 134, 72, 58, 72, 190,
   0, 172, 236, 238, 68, 142, 2, 102,
   0, 170, 48, 184, 34, 82, 110, 60,
   0, 138, 24, 30, 158, 14, 44, 48,
   0, 178, 182, 166, 192, 178, 160, 112]

/-- **The frozen parity `p`** of the triple `(a,b,c)`. -/
def pTable (a b c : ZMod 8) : ZMod 2 :=
  ((pCode.getD (a.val * 8 + b.val) 0 / 2 ^ c.val % 2 : ℕ) : ZMod 2)

/-- A handful of spot checks that the packing is the table it claims to be —
the two hand-worked triples of `RouteBridgeProto` and the exceptional one of
`RouteBridgeNative`, whose parities were computed independently. -/
example : pTable 1 7 1 = 1 := by decide

example : pTable 1 6 1 = 1 := by decide

example : pTable 1 4 4 = 0 := by decide

example : pTable 0 0 0 = 0 := by decide

/-! ## 2. The uniform obligation

One proposition, one shape, for all 512 triples. -/

/-- **`Covered a b c`** — the tabulated parity is realised at `(a,b,c)`: the
intertwiner space at `pTable a b c` is nonzero.

This is the ONLY currency the two construction blocks trade in.  It mentions
neither `gaugeSizeL`/`gaugeSizeR`, nor a frame, nor a connector matrix, so no
consumer of this file can observe which block proved it. -/
def Covered (a b c : ZMod 8) : Prop :=
  gInterSpace ℝ realGauge a b c (pTable a b c) ≠ ⊥

/-- The adapter both blocks are consumed through: a block proves
`gInterSpace … d ≠ ⊥` for the literal parity `d` it computed, and `d` is the
tabulated one. -/
theorem covered_of_eq {a b c : ZMod 8} {d : ZMod 2} (hd : pTable a b c = d)
    (h : gInterSpace ℝ realGauge a b c d ≠ ⊥) : Covered a b c := by
  show gInterSpace ℝ realGauge a b c (pTable a b c) ≠ ⊥
  rw [hd]
  exact h

/-! ## 3. The family

`Ttab` is a nonzero member of the intertwiner space at the tabulated parity.
It is extracted from `Covered` alone, so it is defined by the SAME expression
at all 512 triples — the generic and the exceptional connectors reach it
through the same door. -/

/-- **`Ttab`** — the tabulated connector of the triple `(a,b,c)`: a nonzero
element of `gInterSpace ℝ realGauge a b c (pTable a b c)`. -/
noncomputable def Ttab {a b c : ZMod 8} (h : Covered a b c) :
    GBL realGauge a b c →ₗ[ℝ] GBR realGauge a b c :=
  ((Submodule.ne_bot_iff _).mp h).choose

/-- `Ttab` intertwines the two routes at the tabulated parity: it is a member
of the degree-`pTable a b c` triple intertwiner space, i.e. it is homogeneous
of that degree, super-equivariant for all three slot actions, and right
semilinear along `gaugeCast (add_assoc a b c)`. -/
theorem Ttab_mem {a b c : ZMod 8} (h : Covered a b c) :
    Ttab h ∈ gInterSpace ℝ realGauge a b c (pTable a b c) :=
  ((Submodule.ne_bot_iff _).mp h).choose_spec.1

theorem Ttab_ne_zero {a b c : ZMod 8} (h : Covered a b c) : Ttab h ≠ 0 :=
  ((Submodule.ne_bot_iff _).mp h).choose_spec.2

/-- **The parity is pinned.**  `gParity` — the paper's `p`, defined canonically
as the unique degree at which the Hom super-line is nonzero — equals the
frozen table wherever the table is realised. -/
theorem gParity_eq_pTable {a b c : ZMod 8} (h : Covered a b c) :
    gParity ℝ realGauge a b c = pTable a b c :=
  (gParity_unique ℝ realGauge a b c h).symm

/-- **`connector_bridge`** — the three facts a consumer wants, in one place:
the tabulated data represents the semantic connector (it lies in the
intertwiner space at the tabulated parity), it is nonzero, and it computes
`gParity`. -/
theorem connector_bridge {a b c : ZMod 8} (h : Covered a b c) :
    Ttab h ∈ gInterSpace ℝ realGauge a b c (pTable a b c)
      ∧ Ttab h ≠ 0
      ∧ gParity ℝ realGauge a b c = pTable a b c :=
  ⟨Ttab_mem h, Ttab_ne_zero h, gParity_eq_pTable h⟩

/-! ## 4. The registry — all 512 triples

One line per triple.  Each names a theorem of one of the three sources;
`covered_of_eq (by decide)` checks that the parity that source computed is the
tabulated one, so a certificate proving the WRONG parity cannot be registered
here — the `by decide` would fail.

The twelve exceptional triples sit in the middle of this list spelled exactly
like their generic neighbours; only the module name betrays them. -/

theorem covered_0_0_0 : Covered 0 0 0 :=
  covered_of_eq (by decide) TripleCerts.BatchEasy.gInterSpace0_0_0_ne_bot

theorem covered_0_0_1 : Covered 0 0 1 :=
  covered_of_eq (by decide) TripleCerts.BatchEasy.gInterSpace0_0_1_ne_bot

theorem covered_0_0_2 : Covered 0 0 2 :=
  covered_of_eq (by decide) TripleCerts.BatchEasy.gInterSpace0_0_2_ne_bot

theorem covered_0_0_3 : Covered 0 0 3 :=
  covered_of_eq (by decide) TripleCerts.BatchEasy.gInterSpace0_0_3_ne_bot

theorem covered_0_0_4 : Covered 0 0 4 :=
  covered_of_eq (by decide) TripleCerts.BatchEasy.gInterSpace0_0_4_ne_bot

theorem covered_0_0_5 : Covered 0 0 5 :=
  covered_of_eq (by decide) TripleCerts.BatchEasy.gInterSpace0_0_5_ne_bot

theorem covered_0_0_6 : Covered 0 0 6 :=
  covered_of_eq (by decide) TripleCerts.BatchEasy.gInterSpace0_0_6_ne_bot

theorem covered_0_0_7 : Covered 0 0 7 :=
  covered_of_eq (by decide) TripleCerts.BatchEasy.gInterSpace0_0_7_ne_bot

theorem covered_0_1_0 : Covered 0 1 0 :=
  covered_of_eq (by decide) TripleCerts.G0_1.gInterSpace0_1_0_ne_bot

theorem covered_0_1_1 : Covered 0 1 1 :=
  covered_of_eq (by decide) TripleCerts.G0_1.gInterSpace0_1_1_ne_bot

theorem covered_0_1_2 : Covered 0 1 2 :=
  covered_of_eq (by decide) TripleCerts.G0_1.gInterSpace0_1_2_ne_bot

theorem covered_0_1_3 : Covered 0 1 3 :=
  covered_of_eq (by decide) TripleCerts.G0_1.gInterSpace0_1_3_ne_bot

theorem covered_0_1_4 : Covered 0 1 4 :=
  covered_of_eq (by decide) TripleCerts.G0_1.gInterSpace0_1_4_ne_bot

theorem covered_0_1_5 : Covered 0 1 5 :=
  covered_of_eq (by decide) TripleCerts.G0_1.gInterSpace0_1_5_ne_bot

theorem covered_0_1_6 : Covered 0 1 6 :=
  covered_of_eq (by decide) TripleCerts.G0_1.gInterSpace0_1_6_ne_bot

theorem covered_0_1_7 : Covered 0 1 7 :=
  covered_of_eq (by decide) TripleCerts.G0_1.gInterSpace0_1_7_ne_bot

theorem covered_0_2_0 : Covered 0 2 0 :=
  covered_of_eq (by decide) TripleCerts.G0_1.gInterSpace0_2_0_ne_bot

theorem covered_0_2_1 : Covered 0 2 1 :=
  covered_of_eq (by decide) TripleCerts.G0_1.gInterSpace0_2_1_ne_bot

theorem covered_0_2_2 : Covered 0 2 2 :=
  covered_of_eq (by decide) TripleCerts.G0_1.gInterSpace0_2_2_ne_bot

theorem covered_0_2_3 : Covered 0 2 3 :=
  covered_of_eq (by decide) TripleCerts.G0_1.gInterSpace0_2_3_ne_bot

theorem covered_0_2_4 : Covered 0 2 4 :=
  covered_of_eq (by decide) TripleCerts.G0_1.gInterSpace0_2_4_ne_bot

theorem covered_0_2_5 : Covered 0 2 5 :=
  covered_of_eq (by decide) TripleCerts.G0_1.gInterSpace0_2_5_ne_bot

theorem covered_0_2_6 : Covered 0 2 6 :=
  covered_of_eq (by decide) TripleCerts.G0_1.gInterSpace0_2_6_ne_bot

theorem covered_0_2_7 : Covered 0 2 7 :=
  covered_of_eq (by decide) TripleCerts.G0_1.gInterSpace0_2_7_ne_bot

theorem covered_0_3_0 : Covered 0 3 0 :=
  covered_of_eq (by decide) TripleCerts.G0_1.gInterSpace0_3_0_ne_bot

theorem covered_0_3_1 : Covered 0 3 1 :=
  covered_of_eq (by decide) TripleCerts.G0_1.gInterSpace0_3_1_ne_bot

theorem covered_0_3_2 : Covered 0 3 2 :=
  covered_of_eq (by decide) TripleCerts.G0_1.gInterSpace0_3_2_ne_bot

theorem covered_0_3_3 : Covered 0 3 3 :=
  covered_of_eq (by decide) TripleCerts.G0_1.gInterSpace0_3_3_ne_bot

theorem covered_0_3_4 : Covered 0 3 4 :=
  covered_of_eq (by decide) TripleCerts.G0_1.gInterSpace0_3_4_ne_bot

theorem covered_0_3_5 : Covered 0 3 5 :=
  covered_of_eq (by decide) TripleCerts.G0_1.gInterSpace0_3_5_ne_bot

theorem covered_0_3_6 : Covered 0 3 6 :=
  covered_of_eq (by decide) TripleCerts.G0_1.gInterSpace0_3_6_ne_bot

theorem covered_0_3_7 : Covered 0 3 7 :=
  covered_of_eq (by decide) TripleCerts.G0_2.gInterSpace0_3_7_ne_bot

theorem covered_0_4_0 : Covered 0 4 0 :=
  covered_of_eq (by decide) TripleCerts.G0_2.gInterSpace0_4_0_ne_bot

theorem covered_0_4_1 : Covered 0 4 1 :=
  covered_of_eq (by decide) TripleCerts.G0_2.gInterSpace0_4_1_ne_bot

theorem covered_0_4_2 : Covered 0 4 2 :=
  covered_of_eq (by decide) TripleCerts.G0_2.gInterSpace0_4_2_ne_bot

theorem covered_0_4_3 : Covered 0 4 3 :=
  covered_of_eq (by decide) TripleCerts.G0_2.gInterSpace0_4_3_ne_bot

theorem covered_0_4_4 : Covered 0 4 4 :=
  covered_of_eq (by decide) TripleCerts.G0_2.gInterSpace0_4_4_ne_bot

theorem covered_0_4_5 : Covered 0 4 5 :=
  covered_of_eq (by decide) TripleCerts.G0_2.gInterSpace0_4_5_ne_bot

theorem covered_0_4_6 : Covered 0 4 6 :=
  covered_of_eq (by decide) TripleCerts.G0_2.gInterSpace0_4_6_ne_bot

theorem covered_0_4_7 : Covered 0 4 7 :=
  covered_of_eq (by decide) TripleCerts.G0_2.gInterSpace0_4_7_ne_bot

theorem covered_0_5_0 : Covered 0 5 0 :=
  covered_of_eq (by decide) TripleCerts.G0_2.gInterSpace0_5_0_ne_bot

theorem covered_0_5_1 : Covered 0 5 1 :=
  covered_of_eq (by decide) TripleCerts.G0_2.gInterSpace0_5_1_ne_bot

theorem covered_0_5_2 : Covered 0 5 2 :=
  covered_of_eq (by decide) TripleCerts.G0_2.gInterSpace0_5_2_ne_bot

theorem covered_0_5_3 : Covered 0 5 3 :=
  covered_of_eq (by decide) TripleCerts.G0_2.gInterSpace0_5_3_ne_bot

theorem covered_0_5_4 : Covered 0 5 4 :=
  covered_of_eq (by decide) TripleCerts.G0_2.gInterSpace0_5_4_ne_bot

theorem covered_0_5_5 : Covered 0 5 5 :=
  covered_of_eq (by decide) TripleCerts.G0_2.gInterSpace0_5_5_ne_bot

theorem covered_0_5_6 : Covered 0 5 6 :=
  covered_of_eq (by decide) TripleCerts.G0_2.gInterSpace0_5_6_ne_bot

theorem covered_0_5_7 : Covered 0 5 7 :=
  covered_of_eq (by decide) TripleCerts.G0_2.gInterSpace0_5_7_ne_bot

theorem covered_0_6_0 : Covered 0 6 0 :=
  covered_of_eq (by decide) TripleCerts.G0_2.gInterSpace0_6_0_ne_bot

theorem covered_0_6_1 : Covered 0 6 1 :=
  covered_of_eq (by decide) TripleCerts.G0_2.gInterSpace0_6_1_ne_bot

theorem covered_0_6_2 : Covered 0 6 2 :=
  covered_of_eq (by decide) TripleCerts.G0_2.gInterSpace0_6_2_ne_bot

theorem covered_0_6_3 : Covered 0 6 3 :=
  covered_of_eq (by decide) TripleCerts.G0_3.gInterSpace0_6_3_ne_bot

theorem covered_0_6_4 : Covered 0 6 4 :=
  covered_of_eq (by decide) TripleCerts.G0_3.gInterSpace0_6_4_ne_bot

theorem covered_0_6_5 : Covered 0 6 5 :=
  covered_of_eq (by decide) TripleCerts.G0_3.gInterSpace0_6_5_ne_bot

theorem covered_0_6_6 : Covered 0 6 6 :=
  covered_of_eq (by decide) TripleCerts.G0_3.gInterSpace0_6_6_ne_bot

theorem covered_0_6_7 : Covered 0 6 7 :=
  covered_of_eq (by decide) TripleCerts.G0_3.gInterSpace0_6_7_ne_bot

theorem covered_0_7_0 : Covered 0 7 0 :=
  covered_of_eq (by decide) TripleCerts.G0_3.gInterSpace0_7_0_ne_bot

theorem covered_0_7_1 : Covered 0 7 1 :=
  covered_of_eq (by decide) TripleCerts.G0_3.gInterSpace0_7_1_ne_bot

theorem covered_0_7_2 : Covered 0 7 2 :=
  covered_of_eq (by decide) TripleCerts.G0_3.gInterSpace0_7_2_ne_bot

theorem covered_0_7_3 : Covered 0 7 3 :=
  covered_of_eq (by decide) TripleCerts.G0_3.gInterSpace0_7_3_ne_bot

theorem covered_0_7_4 : Covered 0 7 4 :=
  covered_of_eq (by decide) TripleCerts.G0_3.gInterSpace0_7_4_ne_bot

theorem covered_0_7_5 : Covered 0 7 5 :=
  covered_of_eq (by decide) TripleCerts.G0_3.gInterSpace0_7_5_ne_bot

theorem covered_0_7_6 : Covered 0 7 6 :=
  covered_of_eq (by decide) TripleCerts.G0_3.gInterSpace0_7_6_ne_bot

theorem covered_0_7_7 : Covered 0 7 7 :=
  covered_of_eq (by decide) TripleCerts.G0_3.gInterSpace0_7_7_ne_bot

theorem covered_1_0_0 : Covered 1 0 0 :=
  covered_of_eq (by decide) TripleCerts.G1_1.gInterSpace1_0_0_ne_bot

theorem covered_1_0_1 : Covered 1 0 1 :=
  covered_of_eq (by decide) TripleCerts.G1_1.gInterSpace1_0_1_ne_bot

theorem covered_1_0_2 : Covered 1 0 2 :=
  covered_of_eq (by decide) TripleCerts.G1_1.gInterSpace1_0_2_ne_bot

theorem covered_1_0_3 : Covered 1 0 3 :=
  covered_of_eq (by decide) TripleCerts.G1_1.gInterSpace1_0_3_ne_bot

theorem covered_1_0_4 : Covered 1 0 4 :=
  covered_of_eq (by decide) TripleCerts.G1_1.gInterSpace1_0_4_ne_bot

theorem covered_1_0_5 : Covered 1 0 5 :=
  covered_of_eq (by decide) TripleCerts.G1_1.gInterSpace1_0_5_ne_bot

theorem covered_1_0_6 : Covered 1 0 6 :=
  covered_of_eq (by decide) TripleCerts.G1_1.gInterSpace1_0_6_ne_bot

theorem covered_1_0_7 : Covered 1 0 7 :=
  covered_of_eq (by decide) TripleCerts.G1_1.gInterSpace1_0_7_ne_bot

theorem covered_1_1_0 : Covered 1 1 0 :=
  covered_of_eq (by decide) TripleCerts.Generic1.gInterSpace1_1_0_ne_bot

theorem covered_1_1_1 : Covered 1 1 1 :=
  covered_of_eq (by decide) TripleCerts.Generic1.gInterSpace1_1_1_ne_bot

theorem covered_1_1_2 : Covered 1 1 2 :=
  covered_of_eq (by decide) TripleCerts.Generic1.gInterSpace1_1_2_ne_bot

theorem covered_1_1_3 : Covered 1 1 3 :=
  covered_of_eq (by decide) TripleCerts.Generic1.gInterSpace1_1_3_ne_bot

theorem covered_1_1_4 : Covered 1 1 4 :=
  covered_of_eq (by decide) TripleCerts.Generic1.gInterSpace1_1_4_ne_bot

theorem covered_1_1_5 : Covered 1 1 5 :=
  covered_of_eq (by decide) TripleCerts.Generic1.gInterSpace1_1_5_ne_bot

theorem covered_1_1_6 : Covered 1 1 6 :=
  covered_of_eq (by decide) TripleCerts.Generic1.gInterSpace1_1_6_ne_bot

theorem covered_1_1_7 : Covered 1 1 7 :=
  covered_of_eq (by decide) TripleCerts.Generic1.gInterSpace1_1_7_ne_bot

theorem covered_1_2_0 : Covered 1 2 0 :=
  covered_of_eq (by decide) TripleCerts.G1_1.gInterSpace1_2_0_ne_bot

theorem covered_1_2_1 : Covered 1 2 1 :=
  covered_of_eq (by decide) TripleCerts.G1_1.gInterSpace1_2_1_ne_bot

theorem covered_1_2_2 : Covered 1 2 2 :=
  covered_of_eq (by decide) TripleCerts.G1_1.gInterSpace1_2_2_ne_bot

theorem covered_1_2_3 : Covered 1 2 3 :=
  covered_of_eq (by decide) TripleCerts.BatchMedium.gInterSpace1_2_3_ne_bot

theorem covered_1_2_4 : Covered 1 2 4 :=
  covered_of_eq (by decide) TripleCerts.BatchMedium.gInterSpace1_2_4_ne_bot

theorem covered_1_2_5 : Covered 1 2 5 :=
  covered_of_eq (by decide) TripleCerts.G1_1.gInterSpace1_2_5_ne_bot

theorem covered_1_2_6 : Covered 1 2 6 :=
  covered_of_eq (by decide) TripleCerts.G1_1.gInterSpace1_2_6_ne_bot

theorem covered_1_2_7 : Covered 1 2 7 :=
  covered_of_eq (by decide) TripleCerts.G1_1.gInterSpace1_2_7_ne_bot

theorem covered_1_3_0 : Covered 1 3 0 :=
  covered_of_eq (by decide) TripleCerts.G1_1.gInterSpace1_3_0_ne_bot

theorem covered_1_3_1 : Covered 1 3 1 :=
  covered_of_eq (by decide) TripleCerts.G1_1.gInterSpace1_3_1_ne_bot

theorem covered_1_3_2 : Covered 1 3 2 :=
  covered_of_eq (by decide) TripleCerts.G1_1.gInterSpace1_3_2_ne_bot

theorem covered_1_3_3 : Covered 1 3 3 :=
  covered_of_eq (by decide) TripleCerts.G1_2.gInterSpace1_3_3_ne_bot

theorem covered_1_3_4 : Covered 1 3 4 :=
  covered_of_eq (by decide) TripleCerts.G1_2.gInterSpace1_3_4_ne_bot

theorem covered_1_3_5 : Covered 1 3 5 :=
  covered_of_eq (by decide) TripleCerts.G1_2.gInterSpace1_3_5_ne_bot

theorem covered_1_3_6 : Covered 1 3 6 :=
  covered_of_eq (by decide) TripleCerts.BatchMedium.gInterSpace1_3_6_ne_bot

theorem covered_1_3_7 : Covered 1 3 7 :=
  covered_of_eq (by decide) TripleCerts.G1_2.gInterSpace1_3_7_ne_bot

theorem covered_1_4_0 : Covered 1 4 0 :=
  covered_of_eq (by decide) TripleCerts.G1_2.gInterSpace1_4_0_ne_bot

theorem covered_1_4_1 : Covered 1 4 1 :=
  covered_of_eq (by decide) TripleCerts.G1_2.gInterSpace1_4_1_ne_bot

theorem covered_1_4_2 : Covered 1 4 2 :=
  covered_of_eq (by decide) TripleCerts.BatchMedium.gInterSpace1_4_2_ne_bot

theorem covered_1_4_3 : Covered 1 4 3 :=
  covered_of_eq (by decide) TripleCerts.G1_2.gInterSpace1_4_3_ne_bot

theorem covered_1_4_4 : Covered 1 4 4 :=
  covered_of_eq (by decide) TripleCerts.Exceptional.gInterSpace1_4_4_ne_bot

theorem covered_1_4_5 : Covered 1 4 5 :=
  covered_of_eq (by decide) TripleCerts.G1_3.gInterSpace1_4_5_ne_bot

theorem covered_1_4_6 : Covered 1 4 6 :=
  covered_of_eq (by decide) TripleCerts.G1_3.gInterSpace1_4_6_ne_bot

theorem covered_1_4_7 : Covered 1 4 7 :=
  covered_of_eq (by decide) TripleCerts.G1_3.gInterSpace1_4_7_ne_bot

theorem covered_1_5_0 : Covered 1 5 0 :=
  covered_of_eq (by decide) TripleCerts.G1_3.gInterSpace1_5_0_ne_bot

theorem covered_1_5_1 : Covered 1 5 1 :=
  covered_of_eq (by decide) TripleCerts.G1_3.gInterSpace1_5_1_ne_bot

theorem covered_1_5_2 : Covered 1 5 2 :=
  covered_of_eq (by decide) TripleCerts.G1_3.gInterSpace1_5_2_ne_bot

theorem covered_1_5_3 : Covered 1 5 3 :=
  covered_of_eq (by decide) TripleCerts.G1_3.gInterSpace1_5_3_ne_bot

theorem covered_1_5_4 : Covered 1 5 4 :=
  covered_of_eq (by decide) TripleCerts.BatchMedium.gInterSpace1_5_4_ne_bot

theorem covered_1_5_5 : Covered 1 5 5 :=
  covered_of_eq (by decide) TripleCerts.BatchMedium.gInterSpace1_5_5_ne_bot

theorem covered_1_5_6 : Covered 1 5 6 :=
  covered_of_eq (by decide) TripleCerts.G1_3.gInterSpace1_5_6_ne_bot

theorem covered_1_5_7 : Covered 1 5 7 :=
  covered_of_eq (by decide) TripleCerts.G1_3.gInterSpace1_5_7_ne_bot

theorem covered_1_6_0 : Covered 1 6 0 :=
  covered_of_eq (by decide) TripleCerts.G1_4.gInterSpace1_6_0_ne_bot

theorem covered_1_6_1 : Covered 1 6 1 :=
  covered_of_eq (by decide) gInterSpace161_ne_bot

theorem covered_1_6_2 : Covered 1 6 2 :=
  covered_of_eq (by decide) TripleCerts.G1_4.gInterSpace1_6_2_ne_bot

theorem covered_1_6_3 : Covered 1 6 3 :=
  covered_of_eq (by decide) TripleCerts.G1_4.gInterSpace1_6_3_ne_bot

theorem covered_1_6_4 : Covered 1 6 4 :=
  covered_of_eq (by decide) TripleCerts.G1_4.gInterSpace1_6_4_ne_bot

theorem covered_1_6_5 : Covered 1 6 5 :=
  covered_of_eq (by decide) TripleCerts.G1_4.gInterSpace1_6_5_ne_bot

theorem covered_1_6_6 : Covered 1 6 6 :=
  covered_of_eq (by decide) TripleCerts.G1_4.gInterSpace1_6_6_ne_bot

theorem covered_1_6_7 : Covered 1 6 7 :=
  covered_of_eq (by decide) TripleCerts.G1_4.gInterSpace1_6_7_ne_bot

theorem covered_1_7_0 : Covered 1 7 0 :=
  covered_of_eq (by decide) TripleCerts.G1_4.gInterSpace1_7_0_ne_bot

theorem covered_1_7_1 : Covered 1 7 1 :=
  covered_of_eq (by decide) gInterSpace171_ne_bot

theorem covered_1_7_2 : Covered 1 7 2 :=
  covered_of_eq (by decide) TripleCerts.G1_4.gInterSpace1_7_2_ne_bot

theorem covered_1_7_3 : Covered 1 7 3 :=
  covered_of_eq (by decide) TripleCerts.G1_4.gInterSpace1_7_3_ne_bot

theorem covered_1_7_4 : Covered 1 7 4 :=
  covered_of_eq (by decide) TripleCerts.G1_4.gInterSpace1_7_4_ne_bot

theorem covered_1_7_5 : Covered 1 7 5 :=
  covered_of_eq (by decide) TripleCerts.G1_4.gInterSpace1_7_5_ne_bot

theorem covered_1_7_6 : Covered 1 7 6 :=
  covered_of_eq (by decide) TripleCerts.G1_4.gInterSpace1_7_6_ne_bot

theorem covered_1_7_7 : Covered 1 7 7 :=
  covered_of_eq (by decide) TripleCerts.G1_4.gInterSpace1_7_7_ne_bot

theorem covered_2_0_0 : Covered 2 0 0 :=
  covered_of_eq (by decide) TripleCerts.G2_5.gInterSpace2_0_0_ne_bot

theorem covered_2_0_1 : Covered 2 0 1 :=
  covered_of_eq (by decide) TripleCerts.G2_5.gInterSpace2_0_1_ne_bot

theorem covered_2_0_2 : Covered 2 0 2 :=
  covered_of_eq (by decide) TripleCerts.G2_5.gInterSpace2_0_2_ne_bot

theorem covered_2_0_3 : Covered 2 0 3 :=
  covered_of_eq (by decide) TripleCerts.G2_5.gInterSpace2_0_3_ne_bot

theorem covered_2_0_4 : Covered 2 0 4 :=
  covered_of_eq (by decide) TripleCerts.G2_5.gInterSpace2_0_4_ne_bot

theorem covered_2_0_5 : Covered 2 0 5 :=
  covered_of_eq (by decide) TripleCerts.G2_5.gInterSpace2_0_5_ne_bot

theorem covered_2_0_6 : Covered 2 0 6 :=
  covered_of_eq (by decide) TripleCerts.G2_5.gInterSpace2_0_6_ne_bot

theorem covered_2_0_7 : Covered 2 0 7 :=
  covered_of_eq (by decide) TripleCerts.G2_5.gInterSpace2_0_7_ne_bot

theorem covered_2_1_0 : Covered 2 1 0 :=
  covered_of_eq (by decide) TripleCerts.G2_5.gInterSpace2_1_0_ne_bot

theorem covered_2_1_1 : Covered 2 1 1 :=
  covered_of_eq (by decide) TripleCerts.G2_5.gInterSpace2_1_1_ne_bot

theorem covered_2_1_2 : Covered 2 1 2 :=
  covered_of_eq (by decide) TripleCerts.G2_5.gInterSpace2_1_2_ne_bot

theorem covered_2_1_3 : Covered 2 1 3 :=
  covered_of_eq (by decide) TripleCerts.G2_5.gInterSpace2_1_3_ne_bot

theorem covered_2_1_4 : Covered 2 1 4 :=
  covered_of_eq (by decide) TripleCerts.G2_5.gInterSpace2_1_4_ne_bot

theorem covered_2_1_5 : Covered 2 1 5 :=
  covered_of_eq (by decide) TripleCerts.G2_5.gInterSpace2_1_5_ne_bot

theorem covered_2_1_6 : Covered 2 1 6 :=
  covered_of_eq (by decide) TripleCerts.G2_5.gInterSpace2_1_6_ne_bot

theorem covered_2_1_7 : Covered 2 1 7 :=
  covered_of_eq (by decide) TripleCerts.G2_5.gInterSpace2_1_7_ne_bot

theorem covered_2_2_0 : Covered 2 2 0 :=
  covered_of_eq (by decide) TripleCerts.G2_5.gInterSpace2_2_0_ne_bot

theorem covered_2_2_1 : Covered 2 2 1 :=
  covered_of_eq (by decide) TripleCerts.G2_5.gInterSpace2_2_1_ne_bot

theorem covered_2_2_2 : Covered 2 2 2 :=
  covered_of_eq (by decide) TripleCerts.G2_6.gInterSpace2_2_2_ne_bot

theorem covered_2_2_3 : Covered 2 2 3 :=
  covered_of_eq (by decide) TripleCerts.G2_6.gInterSpace2_2_3_ne_bot

theorem covered_2_2_4 : Covered 2 2 4 :=
  covered_of_eq (by decide) TripleCerts.G2_6.gInterSpace2_2_4_ne_bot

theorem covered_2_2_5 : Covered 2 2 5 :=
  covered_of_eq (by decide) TripleCerts.G2_6.gInterSpace2_2_5_ne_bot

theorem covered_2_2_6 : Covered 2 2 6 :=
  covered_of_eq (by decide) TripleCerts.G2_6.gInterSpace2_2_6_ne_bot

theorem covered_2_2_7 : Covered 2 2 7 :=
  covered_of_eq (by decide) TripleCerts.G2_7.gInterSpace2_2_7_ne_bot

theorem covered_2_3_0 : Covered 2 3 0 :=
  covered_of_eq (by decide) TripleCerts.G2_7.gInterSpace2_3_0_ne_bot

theorem covered_2_3_1 : Covered 2 3 1 :=
  covered_of_eq (by decide) TripleCerts.G2_7.gInterSpace2_3_1_ne_bot

theorem covered_2_3_2 : Covered 2 3 2 :=
  covered_of_eq (by decide) TripleCerts.G2_7.gInterSpace2_3_2_ne_bot

theorem covered_2_3_3 : Covered 2 3 3 :=
  covered_of_eq (by decide) TripleCerts.G2_1.gInterSpace2_3_3_ne_bot

theorem covered_2_3_4 : Covered 2 3 4 :=
  covered_of_eq (by decide) TripleCerts.G2_7.gInterSpace2_3_4_ne_bot

theorem covered_2_3_5 : Covered 2 3 5 :=
  covered_of_eq (by decide) TripleCerts.G2_2.gInterSpace2_3_5_ne_bot

theorem covered_2_3_6 : Covered 2 3 6 :=
  covered_of_eq (by decide) TripleCerts.G2_8.gInterSpace2_3_6_ne_bot

theorem covered_2_3_7 : Covered 2 3 7 :=
  covered_of_eq (by decide) TripleCerts.G2_8.gInterSpace2_3_7_ne_bot

theorem covered_2_4_0 : Covered 2 4 0 :=
  covered_of_eq (by decide) TripleCerts.G2_8.gInterSpace2_4_0_ne_bot

theorem covered_2_4_1 : Covered 2 4 1 :=
  covered_of_eq (by decide) TripleCerts.G2_8.gInterSpace2_4_1_ne_bot

theorem covered_2_4_2 : Covered 2 4 2 :=
  covered_of_eq (by decide) TripleCerts.G2_8.gInterSpace2_4_2_ne_bot

theorem covered_2_4_3 : Covered 2 4 3 :=
  covered_of_eq (by decide) TripleCerts.G2_8.gInterSpace2_4_3_ne_bot

theorem covered_2_4_4 : Covered 2 4 4 :=
  covered_of_eq (by decide) TripleCerts.Exceptional.gInterSpace2_4_4_ne_bot

theorem covered_2_4_5 : Covered 2 4 5 :=
  covered_of_eq (by decide) TripleCerts.G2_9.gInterSpace2_4_5_ne_bot

theorem covered_2_4_6 : Covered 2 4 6 :=
  covered_of_eq (by decide) TripleCerts.G2_9.gInterSpace2_4_6_ne_bot

theorem covered_2_4_7 : Covered 2 4 7 :=
  covered_of_eq (by decide) TripleCerts.G2_9.gInterSpace2_4_7_ne_bot

theorem covered_2_5_0 : Covered 2 5 0 :=
  covered_of_eq (by decide) TripleCerts.G2_9.gInterSpace2_5_0_ne_bot

theorem covered_2_5_1 : Covered 2 5 1 :=
  covered_of_eq (by decide) TripleCerts.G2_9.gInterSpace2_5_1_ne_bot

theorem covered_2_5_2 : Covered 2 5 2 :=
  covered_of_eq (by decide) TripleCerts.G2_9.gInterSpace2_5_2_ne_bot

theorem covered_2_5_3 : Covered 2 5 3 :=
  covered_of_eq (by decide) TripleCerts.G2_3.gInterSpace2_5_3_ne_bot

theorem covered_2_5_4 : Covered 2 5 4 :=
  covered_of_eq (by decide) TripleCerts.G2_10.gInterSpace2_5_4_ne_bot

theorem covered_2_5_5 : Covered 2 5 5 :=
  covered_of_eq (by decide) TripleCerts.G2_4.gInterSpace2_5_5_ne_bot

theorem covered_2_5_6 : Covered 2 5 6 :=
  covered_of_eq (by decide) TripleCerts.G2_10.gInterSpace2_5_6_ne_bot

theorem covered_2_5_7 : Covered 2 5 7 :=
  covered_of_eq (by decide) TripleCerts.G2_10.gInterSpace2_5_7_ne_bot

theorem covered_2_6_0 : Covered 2 6 0 :=
  covered_of_eq (by decide) TripleCerts.G2_10.gInterSpace2_6_0_ne_bot

theorem covered_2_6_1 : Covered 2 6 1 :=
  covered_of_eq (by decide) TripleCerts.G2_10.gInterSpace2_6_1_ne_bot

theorem covered_2_6_2 : Covered 2 6 2 :=
  covered_of_eq (by decide) TripleCerts.G2_10.gInterSpace2_6_2_ne_bot

theorem covered_2_6_3 : Covered 2 6 3 :=
  covered_of_eq (by decide) TripleCerts.G2_11.gInterSpace2_6_3_ne_bot

theorem covered_2_6_4 : Covered 2 6 4 :=
  covered_of_eq (by decide) TripleCerts.G2_11.gInterSpace2_6_4_ne_bot

theorem covered_2_6_5 : Covered 2 6 5 :=
  covered_of_eq (by decide) TripleCerts.G2_11.gInterSpace2_6_5_ne_bot

theorem covered_2_6_6 : Covered 2 6 6 :=
  covered_of_eq (by decide) TripleCerts.G2_11.gInterSpace2_6_6_ne_bot

theorem covered_2_6_7 : Covered 2 6 7 :=
  covered_of_eq (by decide) TripleCerts.G2_11.gInterSpace2_6_7_ne_bot

theorem covered_2_7_0 : Covered 2 7 0 :=
  covered_of_eq (by decide) TripleCerts.G2_11.gInterSpace2_7_0_ne_bot

theorem covered_2_7_1 : Covered 2 7 1 :=
  covered_of_eq (by decide) TripleCerts.G2_11.gInterSpace2_7_1_ne_bot

theorem covered_2_7_2 : Covered 2 7 2 :=
  covered_of_eq (by decide) TripleCerts.G2_12.gInterSpace2_7_2_ne_bot

theorem covered_2_7_3 : Covered 2 7 3 :=
  covered_of_eq (by decide) TripleCerts.G2_12.gInterSpace2_7_3_ne_bot

theorem covered_2_7_4 : Covered 2 7 4 :=
  covered_of_eq (by decide) TripleCerts.G2_12.gInterSpace2_7_4_ne_bot

theorem covered_2_7_5 : Covered 2 7 5 :=
  covered_of_eq (by decide) TripleCerts.G2_12.gInterSpace2_7_5_ne_bot

theorem covered_2_7_6 : Covered 2 7 6 :=
  covered_of_eq (by decide) TripleCerts.G2_12.gInterSpace2_7_6_ne_bot

theorem covered_2_7_7 : Covered 2 7 7 :=
  covered_of_eq (by decide) TripleCerts.G2_12.gInterSpace2_7_7_ne_bot

theorem covered_3_0_0 : Covered 3 0 0 :=
  covered_of_eq (by decide) TripleCerts.G3_14.gInterSpace3_0_0_ne_bot

theorem covered_3_0_1 : Covered 3 0 1 :=
  covered_of_eq (by decide) TripleCerts.G3_14.gInterSpace3_0_1_ne_bot

theorem covered_3_0_2 : Covered 3 0 2 :=
  covered_of_eq (by decide) TripleCerts.G3_14.gInterSpace3_0_2_ne_bot

theorem covered_3_0_3 : Covered 3 0 3 :=
  covered_of_eq (by decide) TripleCerts.G3_14.gInterSpace3_0_3_ne_bot

theorem covered_3_0_4 : Covered 3 0 4 :=
  covered_of_eq (by decide) TripleCerts.G3_14.gInterSpace3_0_4_ne_bot

theorem covered_3_0_5 : Covered 3 0 5 :=
  covered_of_eq (by decide) TripleCerts.G3_14.gInterSpace3_0_5_ne_bot

theorem covered_3_0_6 : Covered 3 0 6 :=
  covered_of_eq (by decide) TripleCerts.G3_14.gInterSpace3_0_6_ne_bot

theorem covered_3_0_7 : Covered 3 0 7 :=
  covered_of_eq (by decide) TripleCerts.G3_14.gInterSpace3_0_7_ne_bot

theorem covered_3_1_0 : Covered 3 1 0 :=
  covered_of_eq (by decide) TripleCerts.G3_14.gInterSpace3_1_0_ne_bot

theorem covered_3_1_1 : Covered 3 1 1 :=
  covered_of_eq (by decide) TripleCerts.G3_14.gInterSpace3_1_1_ne_bot

theorem covered_3_1_2 : Covered 3 1 2 :=
  covered_of_eq (by decide) TripleCerts.G3_14.gInterSpace3_1_2_ne_bot

theorem covered_3_1_3 : Covered 3 1 3 :=
  covered_of_eq (by decide) TripleCerts.G3_15.gInterSpace3_1_3_ne_bot

theorem covered_3_1_4 : Covered 3 1 4 :=
  covered_of_eq (by decide) TripleCerts.G3_15.gInterSpace3_1_4_ne_bot

theorem covered_3_1_5 : Covered 3 1 5 :=
  covered_of_eq (by decide) TripleCerts.G3_15.gInterSpace3_1_5_ne_bot

theorem covered_3_1_6 : Covered 3 1 6 :=
  covered_of_eq (by decide) TripleCerts.G3_15.gInterSpace3_1_6_ne_bot

theorem covered_3_1_7 : Covered 3 1 7 :=
  covered_of_eq (by decide) TripleCerts.G3_15.gInterSpace3_1_7_ne_bot

theorem covered_3_2_0 : Covered 3 2 0 :=
  covered_of_eq (by decide) TripleCerts.G3_15.gInterSpace3_2_0_ne_bot

theorem covered_3_2_1 : Covered 3 2 1 :=
  covered_of_eq (by decide) TripleCerts.G3_16.gInterSpace3_2_1_ne_bot

theorem covered_3_2_2 : Covered 3 2 2 :=
  covered_of_eq (by decide) TripleCerts.G3_16.gInterSpace3_2_2_ne_bot

theorem covered_3_2_3 : Covered 3 2 3 :=
  covered_of_eq (by decide) TripleCerts.G3_1.gInterSpace3_2_3_ne_bot

theorem covered_3_2_4 : Covered 3 2 4 :=
  covered_of_eq (by decide) TripleCerts.G3_16.gInterSpace3_2_4_ne_bot

theorem covered_3_2_5 : Covered 3 2 5 :=
  covered_of_eq (by decide) TripleCerts.G3_2.gInterSpace3_2_5_ne_bot

theorem covered_3_2_6 : Covered 3 2 6 :=
  covered_of_eq (by decide) TripleCerts.G3_16.gInterSpace3_2_6_ne_bot

theorem covered_3_2_7 : Covered 3 2 7 :=
  covered_of_eq (by decide) TripleCerts.G3_17.gInterSpace3_2_7_ne_bot

theorem covered_3_3_0 : Covered 3 3 0 :=
  covered_of_eq (by decide) TripleCerts.G3_17.gInterSpace3_3_0_ne_bot

theorem covered_3_3_1 : Covered 3 3 1 :=
  covered_of_eq (by decide) TripleCerts.G3_17.gInterSpace3_3_1_ne_bot

theorem covered_3_3_2 : Covered 3 3 2 :=
  covered_of_eq (by decide) TripleCerts.G3_3.gInterSpace3_3_2_ne_bot

theorem covered_3_3_3 : Covered 3 3 3 :=
  covered_of_eq (by decide) TripleCerts.G3_4.gInterSpace3_3_3_ne_bot

theorem covered_3_3_4 : Covered 3 3 4 :=
  covered_of_eq (by decide) TripleCerts.G3_5.gInterSpace3_3_4_ne_bot

theorem covered_3_3_5 : Covered 3 3 5 :=
  covered_of_eq (by decide) TripleCerts.BatchHeavy.gInterSpace3_3_5_ne_bot

theorem covered_3_3_6 : Covered 3 3 6 :=
  covered_of_eq (by decide) TripleCerts.G3_6.gInterSpace3_3_6_ne_bot

theorem covered_3_3_7 : Covered 3 3 7 :=
  covered_of_eq (by decide) TripleCerts.G3_17.gInterSpace3_3_7_ne_bot

theorem covered_3_4_0 : Covered 3 4 0 :=
  covered_of_eq (by decide) TripleCerts.G3_17.gInterSpace3_4_0_ne_bot

theorem covered_3_4_1 : Covered 3 4 1 :=
  covered_of_eq (by decide) TripleCerts.G3_18.gInterSpace3_4_1_ne_bot

theorem covered_3_4_2 : Covered 3 4 2 :=
  covered_of_eq (by decide) TripleCerts.G3_18.gInterSpace3_4_2_ne_bot

theorem covered_3_4_3 : Covered 3 4 3 :=
  covered_of_eq (by decide) TripleCerts.G3_7.gInterSpace3_4_3_ne_bot

theorem covered_3_4_4 : Covered 3 4 4 :=
  covered_of_eq (by decide) TripleCerts.Exceptional.gInterSpace3_4_4_ne_bot

theorem covered_3_4_5 : Covered 3 4 5 :=
  covered_of_eq (by decide) TripleCerts.G3_8.gInterSpace3_4_5_ne_bot

theorem covered_3_4_6 : Covered 3 4 6 :=
  covered_of_eq (by decide) TripleCerts.G3_18.gInterSpace3_4_6_ne_bot

theorem covered_3_4_7 : Covered 3 4 7 :=
  covered_of_eq (by decide) TripleCerts.G3_18.gInterSpace3_4_7_ne_bot

theorem covered_3_5_0 : Covered 3 5 0 :=
  covered_of_eq (by decide) TripleCerts.G3_18.gInterSpace3_5_0_ne_bot

theorem covered_3_5_1 : Covered 3 5 1 :=
  covered_of_eq (by decide) TripleCerts.G3_19.gInterSpace3_5_1_ne_bot

theorem covered_3_5_2 : Covered 3 5 2 :=
  covered_of_eq (by decide) TripleCerts.G3_9.gInterSpace3_5_2_ne_bot

theorem covered_3_5_3 : Covered 3 5 3 :=
  covered_of_eq (by decide) TripleCerts.BatchHeavy.gInterSpace3_5_3_ne_bot

theorem covered_3_5_4 : Covered 3 5 4 :=
  covered_of_eq (by decide) TripleCerts.G3_10.gInterSpace3_5_4_ne_bot

theorem covered_3_5_5 : Covered 3 5 5 :=
  covered_of_eq (by decide) TripleCerts.BatchHeavy.gInterSpace3_5_5_ne_bot

theorem covered_3_5_6 : Covered 3 5 6 :=
  covered_of_eq (by decide) TripleCerts.G3_11.gInterSpace3_5_6_ne_bot

theorem covered_3_5_7 : Covered 3 5 7 :=
  covered_of_eq (by decide) TripleCerts.G3_19.gInterSpace3_5_7_ne_bot

theorem covered_3_6_0 : Covered 3 6 0 :=
  covered_of_eq (by decide) TripleCerts.G3_19.gInterSpace3_6_0_ne_bot

theorem covered_3_6_1 : Covered 3 6 1 :=
  covered_of_eq (by decide) TripleCerts.G3_19.gInterSpace3_6_1_ne_bot

theorem covered_3_6_2 : Covered 3 6 2 :=
  covered_of_eq (by decide) TripleCerts.G3_20.gInterSpace3_6_2_ne_bot

theorem covered_3_6_3 : Covered 3 6 3 :=
  covered_of_eq (by decide) TripleCerts.G3_12.gInterSpace3_6_3_ne_bot

theorem covered_3_6_4 : Covered 3 6 4 :=
  covered_of_eq (by decide) TripleCerts.G3_20.gInterSpace3_6_4_ne_bot

theorem covered_3_6_5 : Covered 3 6 5 :=
  covered_of_eq (by decide) TripleCerts.G3_13.gInterSpace3_6_5_ne_bot

theorem covered_3_6_6 : Covered 3 6 6 :=
  covered_of_eq (by decide) TripleCerts.G3_20.gInterSpace3_6_6_ne_bot

theorem covered_3_6_7 : Covered 3 6 7 :=
  covered_of_eq (by decide) TripleCerts.G3_20.gInterSpace3_6_7_ne_bot

theorem covered_3_7_0 : Covered 3 7 0 :=
  covered_of_eq (by decide) TripleCerts.G3_21.gInterSpace3_7_0_ne_bot

theorem covered_3_7_1 : Covered 3 7 1 :=
  covered_of_eq (by decide) TripleCerts.G3_21.gInterSpace3_7_1_ne_bot

theorem covered_3_7_2 : Covered 3 7 2 :=
  covered_of_eq (by decide) TripleCerts.G3_21.gInterSpace3_7_2_ne_bot

theorem covered_3_7_3 : Covered 3 7 3 :=
  covered_of_eq (by decide) TripleCerts.G3_21.gInterSpace3_7_3_ne_bot

theorem covered_3_7_4 : Covered 3 7 4 :=
  covered_of_eq (by decide) TripleCerts.G3_21.gInterSpace3_7_4_ne_bot

theorem covered_3_7_5 : Covered 3 7 5 :=
  covered_of_eq (by decide) TripleCerts.G3_21.gInterSpace3_7_5_ne_bot

theorem covered_3_7_6 : Covered 3 7 6 :=
  covered_of_eq (by decide) TripleCerts.G3_22.gInterSpace3_7_6_ne_bot

theorem covered_3_7_7 : Covered 3 7 7 :=
  covered_of_eq (by decide) TripleCerts.G3_22.gInterSpace3_7_7_ne_bot

theorem covered_4_0_0 : Covered 4 0 0 :=
  covered_of_eq (by decide) TripleCerts.G4_5.gInterSpace4_0_0_ne_bot

theorem covered_4_0_1 : Covered 4 0 1 :=
  covered_of_eq (by decide) TripleCerts.G4_5.gInterSpace4_0_1_ne_bot

theorem covered_4_0_2 : Covered 4 0 2 :=
  covered_of_eq (by decide) TripleCerts.G4_5.gInterSpace4_0_2_ne_bot

theorem covered_4_0_3 : Covered 4 0 3 :=
  covered_of_eq (by decide) TripleCerts.G4_5.gInterSpace4_0_3_ne_bot

theorem covered_4_0_4 : Covered 4 0 4 :=
  covered_of_eq (by decide) TripleCerts.G4_5.gInterSpace4_0_4_ne_bot

theorem covered_4_0_5 : Covered 4 0 5 :=
  covered_of_eq (by decide) TripleCerts.G4_5.gInterSpace4_0_5_ne_bot

theorem covered_4_0_6 : Covered 4 0 6 :=
  covered_of_eq (by decide) TripleCerts.G4_5.gInterSpace4_0_6_ne_bot

theorem covered_4_0_7 : Covered 4 0 7 :=
  covered_of_eq (by decide) TripleCerts.G4_5.gInterSpace4_0_7_ne_bot

theorem covered_4_1_0 : Covered 4 1 0 :=
  covered_of_eq (by decide) TripleCerts.G4_5.gInterSpace4_1_0_ne_bot

theorem covered_4_1_1 : Covered 4 1 1 :=
  covered_of_eq (by decide) TripleCerts.G4_5.gInterSpace4_1_1_ne_bot

theorem covered_4_1_2 : Covered 4 1 2 :=
  covered_of_eq (by decide) TripleCerts.G4_5.gInterSpace4_1_2_ne_bot

theorem covered_4_1_3 : Covered 4 1 3 :=
  covered_of_eq (by decide) TripleCerts.G4_5.gInterSpace4_1_3_ne_bot

theorem covered_4_1_4 : Covered 4 1 4 :=
  covered_of_eq (by decide) TripleCerts.G4_5.gInterSpace4_1_4_ne_bot

theorem covered_4_1_5 : Covered 4 1 5 :=
  covered_of_eq (by decide) TripleCerts.G4_5.gInterSpace4_1_5_ne_bot

theorem covered_4_1_6 : Covered 4 1 6 :=
  covered_of_eq (by decide) TripleCerts.G4_5.gInterSpace4_1_6_ne_bot

theorem covered_4_1_7 : Covered 4 1 7 :=
  covered_of_eq (by decide) TripleCerts.G4_5.gInterSpace4_1_7_ne_bot

theorem covered_4_2_0 : Covered 4 2 0 :=
  covered_of_eq (by decide) TripleCerts.G4_5.gInterSpace4_2_0_ne_bot

theorem covered_4_2_1 : Covered 4 2 1 :=
  covered_of_eq (by decide) TripleCerts.G4_5.gInterSpace4_2_1_ne_bot

theorem covered_4_2_2 : Covered 4 2 2 :=
  covered_of_eq (by decide) TripleCerts.G4_6.gInterSpace4_2_2_ne_bot

theorem covered_4_2_3 : Covered 4 2 3 :=
  covered_of_eq (by decide) TripleCerts.G4_6.gInterSpace4_2_3_ne_bot

theorem covered_4_2_4 : Covered 4 2 4 :=
  covered_of_eq (by decide) TripleCerts.G4_6.gInterSpace4_2_4_ne_bot

theorem covered_4_2_5 : Covered 4 2 5 :=
  covered_of_eq (by decide) TripleCerts.G4_6.gInterSpace4_2_5_ne_bot

theorem covered_4_2_6 : Covered 4 2 6 :=
  covered_of_eq (by decide) TripleCerts.G4_6.gInterSpace4_2_6_ne_bot

theorem covered_4_2_7 : Covered 4 2 7 :=
  covered_of_eq (by decide) TripleCerts.G4_7.gInterSpace4_2_7_ne_bot

theorem covered_4_3_0 : Covered 4 3 0 :=
  covered_of_eq (by decide) TripleCerts.G4_7.gInterSpace4_3_0_ne_bot

theorem covered_4_3_1 : Covered 4 3 1 :=
  covered_of_eq (by decide) TripleCerts.G4_7.gInterSpace4_3_1_ne_bot

theorem covered_4_3_2 : Covered 4 3 2 :=
  covered_of_eq (by decide) TripleCerts.G4_7.gInterSpace4_3_2_ne_bot

theorem covered_4_3_3 : Covered 4 3 3 :=
  covered_of_eq (by decide) TripleCerts.G4_1.gInterSpace4_3_3_ne_bot

theorem covered_4_3_4 : Covered 4 3 4 :=
  covered_of_eq (by decide) TripleCerts.G4_7.gInterSpace4_3_4_ne_bot

theorem covered_4_3_5 : Covered 4 3 5 :=
  covered_of_eq (by decide) TripleCerts.G4_2.gInterSpace4_3_5_ne_bot

theorem covered_4_3_6 : Covered 4 3 6 :=
  covered_of_eq (by decide) TripleCerts.G4_8.gInterSpace4_3_6_ne_bot

theorem covered_4_3_7 : Covered 4 3 7 :=
  covered_of_eq (by decide) TripleCerts.G4_8.gInterSpace4_3_7_ne_bot

theorem covered_4_4_0 : Covered 4 4 0 :=
  covered_of_eq (by decide) TripleCerts.G4_8.gInterSpace4_4_0_ne_bot

theorem covered_4_4_1 : Covered 4 4 1 :=
  covered_of_eq (by decide) TripleCerts.Exceptional.gInterSpace4_4_1_ne_bot

theorem covered_4_4_2 : Covered 4 4 2 :=
  covered_of_eq (by decide) TripleCerts.Exceptional.gInterSpace4_4_2_ne_bot

theorem covered_4_4_3 : Covered 4 4 3 :=
  covered_of_eq (by decide) TripleCerts.Exceptional.gInterSpace4_4_3_ne_bot

theorem covered_4_4_4 : Covered 4 4 4 :=
  covered_of_eq (by decide) TripleCerts.G4_8.gInterSpace4_4_4_ne_bot

theorem covered_4_4_5 : Covered 4 4 5 :=
  covered_of_eq (by decide) TripleCerts.Exceptional.gInterSpace4_4_5_ne_bot

theorem covered_4_4_6 : Covered 4 4 6 :=
  covered_of_eq (by decide) TripleCerts.Exceptional.gInterSpace4_4_6_ne_bot

theorem covered_4_4_7 : Covered 4 4 7 :=
  covered_of_eq (by decide) TripleCerts.Exceptional.gInterSpace4_4_7_ne_bot

theorem covered_4_5_0 : Covered 4 5 0 :=
  covered_of_eq (by decide) TripleCerts.G4_8.gInterSpace4_5_0_ne_bot

theorem covered_4_5_1 : Covered 4 5 1 :=
  covered_of_eq (by decide) TripleCerts.G4_8.gInterSpace4_5_1_ne_bot

theorem covered_4_5_2 : Covered 4 5 2 :=
  covered_of_eq (by decide) TripleCerts.G4_9.gInterSpace4_5_2_ne_bot

theorem covered_4_5_3 : Covered 4 5 3 :=
  covered_of_eq (by decide) TripleCerts.G4_3.gInterSpace4_5_3_ne_bot

theorem covered_4_5_4 : Covered 4 5 4 :=
  covered_of_eq (by decide) TripleCerts.G4_9.gInterSpace4_5_4_ne_bot

theorem covered_4_5_5 : Covered 4 5 5 :=
  covered_of_eq (by decide) TripleCerts.G4_4.gInterSpace4_5_5_ne_bot

theorem covered_4_5_6 : Covered 4 5 6 :=
  covered_of_eq (by decide) TripleCerts.G4_9.gInterSpace4_5_6_ne_bot

theorem covered_4_5_7 : Covered 4 5 7 :=
  covered_of_eq (by decide) TripleCerts.G4_9.gInterSpace4_5_7_ne_bot

theorem covered_4_6_0 : Covered 4 6 0 :=
  covered_of_eq (by decide) TripleCerts.G4_10.gInterSpace4_6_0_ne_bot

theorem covered_4_6_1 : Covered 4 6 1 :=
  covered_of_eq (by decide) TripleCerts.G4_10.gInterSpace4_6_1_ne_bot

theorem covered_4_6_2 : Covered 4 6 2 :=
  covered_of_eq (by decide) TripleCerts.G4_10.gInterSpace4_6_2_ne_bot

theorem covered_4_6_3 : Covered 4 6 3 :=
  covered_of_eq (by decide) TripleCerts.G4_10.gInterSpace4_6_3_ne_bot

theorem covered_4_6_4 : Covered 4 6 4 :=
  covered_of_eq (by decide) TripleCerts.G4_10.gInterSpace4_6_4_ne_bot

theorem covered_4_6_5 : Covered 4 6 5 :=
  covered_of_eq (by decide) TripleCerts.G4_10.gInterSpace4_6_5_ne_bot

theorem covered_4_6_6 : Covered 4 6 6 :=
  covered_of_eq (by decide) TripleCerts.G4_11.gInterSpace4_6_6_ne_bot

theorem covered_4_6_7 : Covered 4 6 7 :=
  covered_of_eq (by decide) TripleCerts.G4_11.gInterSpace4_6_7_ne_bot

theorem covered_4_7_0 : Covered 4 7 0 :=
  covered_of_eq (by decide) TripleCerts.G4_11.gInterSpace4_7_0_ne_bot

theorem covered_4_7_1 : Covered 4 7 1 :=
  covered_of_eq (by decide) TripleCerts.G4_11.gInterSpace4_7_1_ne_bot

theorem covered_4_7_2 : Covered 4 7 2 :=
  covered_of_eq (by decide) TripleCerts.G4_11.gInterSpace4_7_2_ne_bot

theorem covered_4_7_3 : Covered 4 7 3 :=
  covered_of_eq (by decide) TripleCerts.G4_11.gInterSpace4_7_3_ne_bot

theorem covered_4_7_4 : Covered 4 7 4 :=
  covered_of_eq (by decide) TripleCerts.G4_11.gInterSpace4_7_4_ne_bot

theorem covered_4_7_5 : Covered 4 7 5 :=
  covered_of_eq (by decide) TripleCerts.G4_11.gInterSpace4_7_5_ne_bot

theorem covered_4_7_6 : Covered 4 7 6 :=
  covered_of_eq (by decide) TripleCerts.G4_11.gInterSpace4_7_6_ne_bot

theorem covered_4_7_7 : Covered 4 7 7 :=
  covered_of_eq (by decide) TripleCerts.G4_11.gInterSpace4_7_7_ne_bot

theorem covered_5_0_0 : Covered 5 0 0 :=
  covered_of_eq (by decide) TripleCerts.G5_14.gInterSpace5_0_0_ne_bot

theorem covered_5_0_1 : Covered 5 0 1 :=
  covered_of_eq (by decide) TripleCerts.G5_14.gInterSpace5_0_1_ne_bot

theorem covered_5_0_2 : Covered 5 0 2 :=
  covered_of_eq (by decide) TripleCerts.G5_14.gInterSpace5_0_2_ne_bot

theorem covered_5_0_3 : Covered 5 0 3 :=
  covered_of_eq (by decide) TripleCerts.G5_14.gInterSpace5_0_3_ne_bot

theorem covered_5_0_4 : Covered 5 0 4 :=
  covered_of_eq (by decide) TripleCerts.G5_14.gInterSpace5_0_4_ne_bot

theorem covered_5_0_5 : Covered 5 0 5 :=
  covered_of_eq (by decide) TripleCerts.G5_14.gInterSpace5_0_5_ne_bot

theorem covered_5_0_6 : Covered 5 0 6 :=
  covered_of_eq (by decide) TripleCerts.G5_14.gInterSpace5_0_6_ne_bot

theorem covered_5_0_7 : Covered 5 0 7 :=
  covered_of_eq (by decide) TripleCerts.G5_14.gInterSpace5_0_7_ne_bot

theorem covered_5_1_0 : Covered 5 1 0 :=
  covered_of_eq (by decide) TripleCerts.G5_14.gInterSpace5_1_0_ne_bot

theorem covered_5_1_1 : Covered 5 1 1 :=
  covered_of_eq (by decide) TripleCerts.G5_14.gInterSpace5_1_1_ne_bot

theorem covered_5_1_2 : Covered 5 1 2 :=
  covered_of_eq (by decide) TripleCerts.G5_14.gInterSpace5_1_2_ne_bot

theorem covered_5_1_3 : Covered 5 1 3 :=
  covered_of_eq (by decide) TripleCerts.G5_15.gInterSpace5_1_3_ne_bot

theorem covered_5_1_4 : Covered 5 1 4 :=
  covered_of_eq (by decide) TripleCerts.G5_15.gInterSpace5_1_4_ne_bot

theorem covered_5_1_5 : Covered 5 1 5 :=
  covered_of_eq (by decide) TripleCerts.G5_15.gInterSpace5_1_5_ne_bot

theorem covered_5_1_6 : Covered 5 1 6 :=
  covered_of_eq (by decide) TripleCerts.G5_15.gInterSpace5_1_6_ne_bot

theorem covered_5_1_7 : Covered 5 1 7 :=
  covered_of_eq (by decide) TripleCerts.G5_15.gInterSpace5_1_7_ne_bot

theorem covered_5_2_0 : Covered 5 2 0 :=
  covered_of_eq (by decide) TripleCerts.G5_15.gInterSpace5_2_0_ne_bot

theorem covered_5_2_1 : Covered 5 2 1 :=
  covered_of_eq (by decide) TripleCerts.G5_16.gInterSpace5_2_1_ne_bot

theorem covered_5_2_2 : Covered 5 2 2 :=
  covered_of_eq (by decide) TripleCerts.G5_16.gInterSpace5_2_2_ne_bot

theorem covered_5_2_3 : Covered 5 2 3 :=
  covered_of_eq (by decide) TripleCerts.G5_1.gInterSpace5_2_3_ne_bot

theorem covered_5_2_4 : Covered 5 2 4 :=
  covered_of_eq (by decide) TripleCerts.G5_16.gInterSpace5_2_4_ne_bot

theorem covered_5_2_5 : Covered 5 2 5 :=
  covered_of_eq (by decide) TripleCerts.G5_2.gInterSpace5_2_5_ne_bot

theorem covered_5_2_6 : Covered 5 2 6 :=
  covered_of_eq (by decide) TripleCerts.G5_16.gInterSpace5_2_6_ne_bot

theorem covered_5_2_7 : Covered 5 2 7 :=
  covered_of_eq (by decide) TripleCerts.G5_17.gInterSpace5_2_7_ne_bot

theorem covered_5_3_0 : Covered 5 3 0 :=
  covered_of_eq (by decide) TripleCerts.G5_17.gInterSpace5_3_0_ne_bot

theorem covered_5_3_1 : Covered 5 3 1 :=
  covered_of_eq (by decide) TripleCerts.G5_17.gInterSpace5_3_1_ne_bot

theorem covered_5_3_2 : Covered 5 3 2 :=
  covered_of_eq (by decide) TripleCerts.G5_3.gInterSpace5_3_2_ne_bot

theorem covered_5_3_3 : Covered 5 3 3 :=
  covered_of_eq (by decide) TripleCerts.BatchHeavy.gInterSpace5_3_3_ne_bot

theorem covered_5_3_4 : Covered 5 3 4 :=
  covered_of_eq (by decide) TripleCerts.G5_4.gInterSpace5_3_4_ne_bot

theorem covered_5_3_5 : Covered 5 3 5 :=
  covered_of_eq (by decide) TripleCerts.BatchHeavy.gInterSpace5_3_5_ne_bot

theorem covered_5_3_6 : Covered 5 3 6 :=
  covered_of_eq (by decide) TripleCerts.G5_5.gInterSpace5_3_6_ne_bot

theorem covered_5_3_7 : Covered 5 3 7 :=
  covered_of_eq (by decide) TripleCerts.G5_17.gInterSpace5_3_7_ne_bot

theorem covered_5_4_0 : Covered 5 4 0 :=
  covered_of_eq (by decide) TripleCerts.G5_17.gInterSpace5_4_0_ne_bot

theorem covered_5_4_1 : Covered 5 4 1 :=
  covered_of_eq (by decide) TripleCerts.G5_18.gInterSpace5_4_1_ne_bot

theorem covered_5_4_2 : Covered 5 4 2 :=
  covered_of_eq (by decide) TripleCerts.G5_18.gInterSpace5_4_2_ne_bot

theorem covered_5_4_3 : Covered 5 4 3 :=
  covered_of_eq (by decide) TripleCerts.G5_6.gInterSpace5_4_3_ne_bot

theorem covered_5_4_4 : Covered 5 4 4 :=
  covered_of_eq (by decide) TripleCerts.Exceptional.gInterSpace5_4_4_ne_bot

theorem covered_5_4_5 : Covered 5 4 5 :=
  covered_of_eq (by decide) TripleCerts.G5_7.gInterSpace5_4_5_ne_bot

theorem covered_5_4_6 : Covered 5 4 6 :=
  covered_of_eq (by decide) TripleCerts.G5_18.gInterSpace5_4_6_ne_bot

theorem covered_5_4_7 : Covered 5 4 7 :=
  covered_of_eq (by decide) TripleCerts.G5_18.gInterSpace5_4_7_ne_bot

theorem covered_5_5_0 : Covered 5 5 0 :=
  covered_of_eq (by decide) TripleCerts.G5_18.gInterSpace5_5_0_ne_bot

theorem covered_5_5_1 : Covered 5 5 1 :=
  covered_of_eq (by decide) TripleCerts.G5_19.gInterSpace5_5_1_ne_bot

theorem covered_5_5_2 : Covered 5 5 2 :=
  covered_of_eq (by decide) TripleCerts.G5_8.gInterSpace5_5_2_ne_bot

theorem covered_5_5_3 : Covered 5 5 3 :=
  covered_of_eq (by decide) TripleCerts.BatchHeavy.gInterSpace5_5_3_ne_bot

theorem covered_5_5_4 : Covered 5 5 4 :=
  covered_of_eq (by decide) TripleCerts.G5_9.gInterSpace5_5_4_ne_bot

theorem covered_5_5_5 : Covered 5 5 5 :=
  covered_of_eq (by decide) TripleCerts.G5_10.gInterSpace5_5_5_ne_bot

theorem covered_5_5_6 : Covered 5 5 6 :=
  covered_of_eq (by decide) TripleCerts.G5_11.gInterSpace5_5_6_ne_bot

theorem covered_5_5_7 : Covered 5 5 7 :=
  covered_of_eq (by decide) TripleCerts.G5_19.gInterSpace5_5_7_ne_bot

theorem covered_5_6_0 : Covered 5 6 0 :=
  covered_of_eq (by decide) TripleCerts.G5_19.gInterSpace5_6_0_ne_bot

theorem covered_5_6_1 : Covered 5 6 1 :=
  covered_of_eq (by decide) TripleCerts.G5_19.gInterSpace5_6_1_ne_bot

theorem covered_5_6_2 : Covered 5 6 2 :=
  covered_of_eq (by decide) TripleCerts.G5_20.gInterSpace5_6_2_ne_bot

theorem covered_5_6_3 : Covered 5 6 3 :=
  covered_of_eq (by decide) TripleCerts.G5_12.gInterSpace5_6_3_ne_bot

theorem covered_5_6_4 : Covered 5 6 4 :=
  covered_of_eq (by decide) TripleCerts.G5_20.gInterSpace5_6_4_ne_bot

theorem covered_5_6_5 : Covered 5 6 5 :=
  covered_of_eq (by decide) TripleCerts.G5_13.gInterSpace5_6_5_ne_bot

theorem covered_5_6_6 : Covered 5 6 6 :=
  covered_of_eq (by decide) TripleCerts.G5_20.gInterSpace5_6_6_ne_bot

theorem covered_5_6_7 : Covered 5 6 7 :=
  covered_of_eq (by decide) TripleCerts.G5_20.gInterSpace5_6_7_ne_bot

theorem covered_5_7_0 : Covered 5 7 0 :=
  covered_of_eq (by decide) TripleCerts.G5_21.gInterSpace5_7_0_ne_bot

theorem covered_5_7_1 : Covered 5 7 1 :=
  covered_of_eq (by decide) TripleCerts.G5_21.gInterSpace5_7_1_ne_bot

theorem covered_5_7_2 : Covered 5 7 2 :=
  covered_of_eq (by decide) TripleCerts.G5_21.gInterSpace5_7_2_ne_bot

theorem covered_5_7_3 : Covered 5 7 3 :=
  covered_of_eq (by decide) TripleCerts.G5_21.gInterSpace5_7_3_ne_bot

theorem covered_5_7_4 : Covered 5 7 4 :=
  covered_of_eq (by decide) TripleCerts.G5_21.gInterSpace5_7_4_ne_bot

theorem covered_5_7_5 : Covered 5 7 5 :=
  covered_of_eq (by decide) TripleCerts.G5_21.gInterSpace5_7_5_ne_bot

theorem covered_5_7_6 : Covered 5 7 6 :=
  covered_of_eq (by decide) TripleCerts.G5_22.gInterSpace5_7_6_ne_bot

theorem covered_5_7_7 : Covered 5 7 7 :=
  covered_of_eq (by decide) TripleCerts.G5_22.gInterSpace5_7_7_ne_bot

theorem covered_6_0_0 : Covered 6 0 0 :=
  covered_of_eq (by decide) TripleCerts.G6_5.gInterSpace6_0_0_ne_bot

theorem covered_6_0_1 : Covered 6 0 1 :=
  covered_of_eq (by decide) TripleCerts.G6_5.gInterSpace6_0_1_ne_bot

theorem covered_6_0_2 : Covered 6 0 2 :=
  covered_of_eq (by decide) TripleCerts.G6_5.gInterSpace6_0_2_ne_bot

theorem covered_6_0_3 : Covered 6 0 3 :=
  covered_of_eq (by decide) TripleCerts.G6_5.gInterSpace6_0_3_ne_bot

theorem covered_6_0_4 : Covered 6 0 4 :=
  covered_of_eq (by decide) TripleCerts.G6_5.gInterSpace6_0_4_ne_bot

theorem covered_6_0_5 : Covered 6 0 5 :=
  covered_of_eq (by decide) TripleCerts.G6_5.gInterSpace6_0_5_ne_bot

theorem covered_6_0_6 : Covered 6 0 6 :=
  covered_of_eq (by decide) TripleCerts.G6_5.gInterSpace6_0_6_ne_bot

theorem covered_6_0_7 : Covered 6 0 7 :=
  covered_of_eq (by decide) TripleCerts.G6_5.gInterSpace6_0_7_ne_bot

theorem covered_6_1_0 : Covered 6 1 0 :=
  covered_of_eq (by decide) TripleCerts.G6_5.gInterSpace6_1_0_ne_bot

theorem covered_6_1_1 : Covered 6 1 1 :=
  covered_of_eq (by decide) TripleCerts.G6_5.gInterSpace6_1_1_ne_bot

theorem covered_6_1_2 : Covered 6 1 2 :=
  covered_of_eq (by decide) TripleCerts.G6_5.gInterSpace6_1_2_ne_bot

theorem covered_6_1_3 : Covered 6 1 3 :=
  covered_of_eq (by decide) TripleCerts.G6_5.gInterSpace6_1_3_ne_bot

theorem covered_6_1_4 : Covered 6 1 4 :=
  covered_of_eq (by decide) TripleCerts.G6_5.gInterSpace6_1_4_ne_bot

theorem covered_6_1_5 : Covered 6 1 5 :=
  covered_of_eq (by decide) TripleCerts.G6_5.gInterSpace6_1_5_ne_bot

theorem covered_6_1_6 : Covered 6 1 6 :=
  covered_of_eq (by decide) TripleCerts.G6_5.gInterSpace6_1_6_ne_bot

theorem covered_6_1_7 : Covered 6 1 7 :=
  covered_of_eq (by decide) TripleCerts.G6_5.gInterSpace6_1_7_ne_bot

theorem covered_6_2_0 : Covered 6 2 0 :=
  covered_of_eq (by decide) TripleCerts.G6_5.gInterSpace6_2_0_ne_bot

theorem covered_6_2_1 : Covered 6 2 1 :=
  covered_of_eq (by decide) TripleCerts.G6_5.gInterSpace6_2_1_ne_bot

theorem covered_6_2_2 : Covered 6 2 2 :=
  covered_of_eq (by decide) TripleCerts.G6_6.gInterSpace6_2_2_ne_bot

theorem covered_6_2_3 : Covered 6 2 3 :=
  covered_of_eq (by decide) TripleCerts.G6_6.gInterSpace6_2_3_ne_bot

theorem covered_6_2_4 : Covered 6 2 4 :=
  covered_of_eq (by decide) TripleCerts.G6_6.gInterSpace6_2_4_ne_bot

theorem covered_6_2_5 : Covered 6 2 5 :=
  covered_of_eq (by decide) TripleCerts.G6_6.gInterSpace6_2_5_ne_bot

theorem covered_6_2_6 : Covered 6 2 6 :=
  covered_of_eq (by decide) TripleCerts.G6_6.gInterSpace6_2_6_ne_bot

theorem covered_6_2_7 : Covered 6 2 7 :=
  covered_of_eq (by decide) TripleCerts.G6_7.gInterSpace6_2_7_ne_bot

theorem covered_6_3_0 : Covered 6 3 0 :=
  covered_of_eq (by decide) TripleCerts.G6_7.gInterSpace6_3_0_ne_bot

theorem covered_6_3_1 : Covered 6 3 1 :=
  covered_of_eq (by decide) TripleCerts.G6_7.gInterSpace6_3_1_ne_bot

theorem covered_6_3_2 : Covered 6 3 2 :=
  covered_of_eq (by decide) TripleCerts.G6_7.gInterSpace6_3_2_ne_bot

theorem covered_6_3_3 : Covered 6 3 3 :=
  covered_of_eq (by decide) TripleCerts.G6_1.gInterSpace6_3_3_ne_bot

theorem covered_6_3_4 : Covered 6 3 4 :=
  covered_of_eq (by decide) TripleCerts.G6_7.gInterSpace6_3_4_ne_bot

theorem covered_6_3_5 : Covered 6 3 5 :=
  covered_of_eq (by decide) TripleCerts.G6_2.gInterSpace6_3_5_ne_bot

theorem covered_6_3_6 : Covered 6 3 6 :=
  covered_of_eq (by decide) TripleCerts.G6_8.gInterSpace6_3_6_ne_bot

theorem covered_6_3_7 : Covered 6 3 7 :=
  covered_of_eq (by decide) TripleCerts.G6_8.gInterSpace6_3_7_ne_bot

theorem covered_6_4_0 : Covered 6 4 0 :=
  covered_of_eq (by decide) TripleCerts.G6_8.gInterSpace6_4_0_ne_bot

theorem covered_6_4_1 : Covered 6 4 1 :=
  covered_of_eq (by decide) TripleCerts.G6_8.gInterSpace6_4_1_ne_bot

theorem covered_6_4_2 : Covered 6 4 2 :=
  covered_of_eq (by decide) TripleCerts.G6_8.gInterSpace6_4_2_ne_bot

theorem covered_6_4_3 : Covered 6 4 3 :=
  covered_of_eq (by decide) TripleCerts.G6_8.gInterSpace6_4_3_ne_bot

theorem covered_6_4_4 : Covered 6 4 4 :=
  covered_of_eq (by decide) TripleCerts.Exceptional.gInterSpace6_4_4_ne_bot

theorem covered_6_4_5 : Covered 6 4 5 :=
  covered_of_eq (by decide) TripleCerts.G6_9.gInterSpace6_4_5_ne_bot

theorem covered_6_4_6 : Covered 6 4 6 :=
  covered_of_eq (by decide) TripleCerts.G6_9.gInterSpace6_4_6_ne_bot

theorem covered_6_4_7 : Covered 6 4 7 :=
  covered_of_eq (by decide) TripleCerts.G6_9.gInterSpace6_4_7_ne_bot

theorem covered_6_5_0 : Covered 6 5 0 :=
  covered_of_eq (by decide) TripleCerts.G6_9.gInterSpace6_5_0_ne_bot

theorem covered_6_5_1 : Covered 6 5 1 :=
  covered_of_eq (by decide) TripleCerts.G6_9.gInterSpace6_5_1_ne_bot

theorem covered_6_5_2 : Covered 6 5 2 :=
  covered_of_eq (by decide) TripleCerts.G6_9.gInterSpace6_5_2_ne_bot

theorem covered_6_5_3 : Covered 6 5 3 :=
  covered_of_eq (by decide) TripleCerts.G6_3.gInterSpace6_5_3_ne_bot

theorem covered_6_5_4 : Covered 6 5 4 :=
  covered_of_eq (by decide) TripleCerts.G6_10.gInterSpace6_5_4_ne_bot

theorem covered_6_5_5 : Covered 6 5 5 :=
  covered_of_eq (by decide) TripleCerts.G6_4.gInterSpace6_5_5_ne_bot

theorem covered_6_5_6 : Covered 6 5 6 :=
  covered_of_eq (by decide) TripleCerts.G6_10.gInterSpace6_5_6_ne_bot

theorem covered_6_5_7 : Covered 6 5 7 :=
  covered_of_eq (by decide) TripleCerts.G6_10.gInterSpace6_5_7_ne_bot

theorem covered_6_6_0 : Covered 6 6 0 :=
  covered_of_eq (by decide) TripleCerts.G6_10.gInterSpace6_6_0_ne_bot

theorem covered_6_6_1 : Covered 6 6 1 :=
  covered_of_eq (by decide) TripleCerts.G6_10.gInterSpace6_6_1_ne_bot

theorem covered_6_6_2 : Covered 6 6 2 :=
  covered_of_eq (by decide) TripleCerts.G6_10.gInterSpace6_6_2_ne_bot

theorem covered_6_6_3 : Covered 6 6 3 :=
  covered_of_eq (by decide) TripleCerts.G6_11.gInterSpace6_6_3_ne_bot

theorem covered_6_6_4 : Covered 6 6 4 :=
  covered_of_eq (by decide) TripleCerts.G6_11.gInterSpace6_6_4_ne_bot

theorem covered_6_6_5 : Covered 6 6 5 :=
  covered_of_eq (by decide) TripleCerts.G6_11.gInterSpace6_6_5_ne_bot

theorem covered_6_6_6 : Covered 6 6 6 :=
  covered_of_eq (by decide) TripleCerts.G6_11.gInterSpace6_6_6_ne_bot

theorem covered_6_6_7 : Covered 6 6 7 :=
  covered_of_eq (by decide) TripleCerts.G6_11.gInterSpace6_6_7_ne_bot

theorem covered_6_7_0 : Covered 6 7 0 :=
  covered_of_eq (by decide) TripleCerts.G6_11.gInterSpace6_7_0_ne_bot

theorem covered_6_7_1 : Covered 6 7 1 :=
  covered_of_eq (by decide) TripleCerts.G6_11.gInterSpace6_7_1_ne_bot

theorem covered_6_7_2 : Covered 6 7 2 :=
  covered_of_eq (by decide) TripleCerts.G6_12.gInterSpace6_7_2_ne_bot

theorem covered_6_7_3 : Covered 6 7 3 :=
  covered_of_eq (by decide) TripleCerts.G6_12.gInterSpace6_7_3_ne_bot

theorem covered_6_7_4 : Covered 6 7 4 :=
  covered_of_eq (by decide) TripleCerts.G6_12.gInterSpace6_7_4_ne_bot

theorem covered_6_7_5 : Covered 6 7 5 :=
  covered_of_eq (by decide) TripleCerts.G6_12.gInterSpace6_7_5_ne_bot

theorem covered_6_7_6 : Covered 6 7 6 :=
  covered_of_eq (by decide) TripleCerts.G6_12.gInterSpace6_7_6_ne_bot

theorem covered_6_7_7 : Covered 6 7 7 :=
  covered_of_eq (by decide) TripleCerts.G6_12.gInterSpace6_7_7_ne_bot

theorem covered_7_0_0 : Covered 7 0 0 :=
  covered_of_eq (by decide) TripleCerts.G7_1.gInterSpace7_0_0_ne_bot

theorem covered_7_0_1 : Covered 7 0 1 :=
  covered_of_eq (by decide) TripleCerts.G7_1.gInterSpace7_0_1_ne_bot

theorem covered_7_0_2 : Covered 7 0 2 :=
  covered_of_eq (by decide) TripleCerts.G7_1.gInterSpace7_0_2_ne_bot

theorem covered_7_0_3 : Covered 7 0 3 :=
  covered_of_eq (by decide) TripleCerts.G7_1.gInterSpace7_0_3_ne_bot

theorem covered_7_0_4 : Covered 7 0 4 :=
  covered_of_eq (by decide) TripleCerts.G7_1.gInterSpace7_0_4_ne_bot

theorem covered_7_0_5 : Covered 7 0 5 :=
  covered_of_eq (by decide) TripleCerts.G7_1.gInterSpace7_0_5_ne_bot

theorem covered_7_0_6 : Covered 7 0 6 :=
  covered_of_eq (by decide) TripleCerts.G7_1.gInterSpace7_0_6_ne_bot

theorem covered_7_0_7 : Covered 7 0 7 :=
  covered_of_eq (by decide) TripleCerts.G7_1.gInterSpace7_0_7_ne_bot

theorem covered_7_1_0 : Covered 7 1 0 :=
  covered_of_eq (by decide) TripleCerts.G7_1.gInterSpace7_1_0_ne_bot

theorem covered_7_1_1 : Covered 7 1 1 :=
  covered_of_eq (by decide) TripleCerts.G7_1.gInterSpace7_1_1_ne_bot

theorem covered_7_1_2 : Covered 7 1 2 :=
  covered_of_eq (by decide) TripleCerts.G7_1.gInterSpace7_1_2_ne_bot

theorem covered_7_1_3 : Covered 7 1 3 :=
  covered_of_eq (by decide) TripleCerts.G7_1.gInterSpace7_1_3_ne_bot

theorem covered_7_1_4 : Covered 7 1 4 :=
  covered_of_eq (by decide) TripleCerts.G7_1.gInterSpace7_1_4_ne_bot

theorem covered_7_1_5 : Covered 7 1 5 :=
  covered_of_eq (by decide) TripleCerts.G7_1.gInterSpace7_1_5_ne_bot

theorem covered_7_1_6 : Covered 7 1 6 :=
  covered_of_eq (by decide) TripleCerts.G7_1.gInterSpace7_1_6_ne_bot

theorem covered_7_1_7 : Covered 7 1 7 :=
  covered_of_eq (by decide) TripleCerts.G7_1.gInterSpace7_1_7_ne_bot

theorem covered_7_2_0 : Covered 7 2 0 :=
  covered_of_eq (by decide) TripleCerts.G7_1.gInterSpace7_2_0_ne_bot

theorem covered_7_2_1 : Covered 7 2 1 :=
  covered_of_eq (by decide) TripleCerts.G7_1.gInterSpace7_2_1_ne_bot

theorem covered_7_2_2 : Covered 7 2 2 :=
  covered_of_eq (by decide) TripleCerts.G7_1.gInterSpace7_2_2_ne_bot

theorem covered_7_2_3 : Covered 7 2 3 :=
  covered_of_eq (by decide) TripleCerts.G7_1.gInterSpace7_2_3_ne_bot

theorem covered_7_2_4 : Covered 7 2 4 :=
  covered_of_eq (by decide) TripleCerts.G7_1.gInterSpace7_2_4_ne_bot

theorem covered_7_2_5 : Covered 7 2 5 :=
  covered_of_eq (by decide) TripleCerts.G7_1.gInterSpace7_2_5_ne_bot

theorem covered_7_2_6 : Covered 7 2 6 :=
  covered_of_eq (by decide) TripleCerts.G7_1.gInterSpace7_2_6_ne_bot

theorem covered_7_2_7 : Covered 7 2 7 :=
  covered_of_eq (by decide) TripleCerts.G7_2.gInterSpace7_2_7_ne_bot

theorem covered_7_3_0 : Covered 7 3 0 :=
  covered_of_eq (by decide) TripleCerts.G7_2.gInterSpace7_3_0_ne_bot

theorem covered_7_3_1 : Covered 7 3 1 :=
  covered_of_eq (by decide) TripleCerts.G7_2.gInterSpace7_3_1_ne_bot

theorem covered_7_3_2 : Covered 7 3 2 :=
  covered_of_eq (by decide) TripleCerts.G7_2.gInterSpace7_3_2_ne_bot

theorem covered_7_3_3 : Covered 7 3 3 :=
  covered_of_eq (by decide) TripleCerts.G7_2.gInterSpace7_3_3_ne_bot

theorem covered_7_3_4 : Covered 7 3 4 :=
  covered_of_eq (by decide) TripleCerts.G7_2.gInterSpace7_3_4_ne_bot

theorem covered_7_3_5 : Covered 7 3 5 :=
  covered_of_eq (by decide) TripleCerts.G7_2.gInterSpace7_3_5_ne_bot

theorem covered_7_3_6 : Covered 7 3 6 :=
  covered_of_eq (by decide) TripleCerts.G7_3.gInterSpace7_3_6_ne_bot

theorem covered_7_3_7 : Covered 7 3 7 :=
  covered_of_eq (by decide) TripleCerts.G7_3.gInterSpace7_3_7_ne_bot

theorem covered_7_4_0 : Covered 7 4 0 :=
  covered_of_eq (by decide) TripleCerts.G7_3.gInterSpace7_4_0_ne_bot

theorem covered_7_4_1 : Covered 7 4 1 :=
  covered_of_eq (by decide) TripleCerts.G7_3.gInterSpace7_4_1_ne_bot

theorem covered_7_4_2 : Covered 7 4 2 :=
  covered_of_eq (by decide) TripleCerts.G7_3.gInterSpace7_4_2_ne_bot

theorem covered_7_4_3 : Covered 7 4 3 :=
  covered_of_eq (by decide) TripleCerts.G7_3.gInterSpace7_4_3_ne_bot

theorem covered_7_4_4 : Covered 7 4 4 :=
  covered_of_eq (by decide) TripleCerts.Exceptional.gInterSpace7_4_4_ne_bot

theorem covered_7_4_5 : Covered 7 4 5 :=
  covered_of_eq (by decide) TripleCerts.G7_3.gInterSpace7_4_5_ne_bot

theorem covered_7_4_6 : Covered 7 4 6 :=
  covered_of_eq (by decide) TripleCerts.G7_3.gInterSpace7_4_6_ne_bot

theorem covered_7_4_7 : Covered 7 4 7 :=
  covered_of_eq (by decide) TripleCerts.G7_3.gInterSpace7_4_7_ne_bot

theorem covered_7_5_0 : Covered 7 5 0 :=
  covered_of_eq (by decide) TripleCerts.G7_3.gInterSpace7_5_0_ne_bot

theorem covered_7_5_1 : Covered 7 5 1 :=
  covered_of_eq (by decide) TripleCerts.G7_3.gInterSpace7_5_1_ne_bot

theorem covered_7_5_2 : Covered 7 5 2 :=
  covered_of_eq (by decide) TripleCerts.G7_3.gInterSpace7_5_2_ne_bot

theorem covered_7_5_3 : Covered 7 5 3 :=
  covered_of_eq (by decide) TripleCerts.G7_4.gInterSpace7_5_3_ne_bot

theorem covered_7_5_4 : Covered 7 5 4 :=
  covered_of_eq (by decide) TripleCerts.G7_4.gInterSpace7_5_4_ne_bot

theorem covered_7_5_5 : Covered 7 5 5 :=
  covered_of_eq (by decide) TripleCerts.G7_4.gInterSpace7_5_5_ne_bot

theorem covered_7_5_6 : Covered 7 5 6 :=
  covered_of_eq (by decide) TripleCerts.G7_4.gInterSpace7_5_6_ne_bot

theorem covered_7_5_7 : Covered 7 5 7 :=
  covered_of_eq (by decide) TripleCerts.G7_4.gInterSpace7_5_7_ne_bot

theorem covered_7_6_0 : Covered 7 6 0 :=
  covered_of_eq (by decide) TripleCerts.G7_4.gInterSpace7_6_0_ne_bot

theorem covered_7_6_1 : Covered 7 6 1 :=
  covered_of_eq (by decide) TripleCerts.G7_4.gInterSpace7_6_1_ne_bot

theorem covered_7_6_2 : Covered 7 6 2 :=
  covered_of_eq (by decide) TripleCerts.G7_5.gInterSpace7_6_2_ne_bot

theorem covered_7_6_3 : Covered 7 6 3 :=
  covered_of_eq (by decide) TripleCerts.G7_5.gInterSpace7_6_3_ne_bot

theorem covered_7_6_4 : Covered 7 6 4 :=
  covered_of_eq (by decide) TripleCerts.G7_5.gInterSpace7_6_4_ne_bot

theorem covered_7_6_5 : Covered 7 6 5 :=
  covered_of_eq (by decide) TripleCerts.G7_5.gInterSpace7_6_5_ne_bot

theorem covered_7_6_6 : Covered 7 6 6 :=
  covered_of_eq (by decide) TripleCerts.G7_5.gInterSpace7_6_6_ne_bot

theorem covered_7_6_7 : Covered 7 6 7 :=
  covered_of_eq (by decide) TripleCerts.G7_5.gInterSpace7_6_7_ne_bot

theorem covered_7_7_0 : Covered 7 7 0 :=
  covered_of_eq (by decide) TripleCerts.G7_5.gInterSpace7_7_0_ne_bot

theorem covered_7_7_1 : Covered 7 7 1 :=
  covered_of_eq (by decide) TripleCerts.G7_5.gInterSpace7_7_1_ne_bot

theorem covered_7_7_2 : Covered 7 7 2 :=
  covered_of_eq (by decide) TripleCerts.G7_5.gInterSpace7_7_2_ne_bot

theorem covered_7_7_3 : Covered 7 7 3 :=
  covered_of_eq (by decide) TripleCerts.G7_5.gInterSpace7_7_3_ne_bot

theorem covered_7_7_4 : Covered 7 7 4 :=
  covered_of_eq (by decide) TripleCerts.G7_5.gInterSpace7_7_4_ne_bot

theorem covered_7_7_5 : Covered 7 7 5 :=
  covered_of_eq (by decide) TripleCerts.G7_5.gInterSpace7_7_5_ne_bot

theorem covered_7_7_6 : Covered 7 7 6 :=
  covered_of_eq (by decide) TripleCerts.G7_5.gInterSpace7_7_6_ne_bot

theorem covered_7_7_7 : Covered 7 7 7 :=
  covered_of_eq (by decide) TripleCerts.G7_5.gInterSpace7_7_7_ne_bot

/-! ## 5. Dispatch

`Covered` is not decidable, so the 512 cases cannot be discharged by `decide`;
they have to be enumerated.  Doing that with one 512-way `fin_cases` is
quadratic in pain, so the case split is factored: `zmod8_cases` is proved ONCE
and then applied 1 + 8 + 64 = 73 times, purely in term mode.  Nothing here is
a tactic block that grows with the table. -/

/-- Eight-way case analysis on `ZMod 8`, proved once. -/
theorem zmod8_cases {P : ZMod 8 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2)
    (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) : ∀ x, P x := by
  intro x
  fin_cases x
  exacts [h0, h1, h2, h3, h4, h5, h6, h7]

/-! ### 5.1 Fixing `a` and `b`, over all `c` (64 lemmas) -/

theorem covered_0_0 : ∀ c : ZMod 8, Covered 0 0 c :=
  zmod8_cases covered_0_0_0 covered_0_0_1 covered_0_0_2 covered_0_0_3
    covered_0_0_4 covered_0_0_5 covered_0_0_6 covered_0_0_7

theorem covered_0_1 : ∀ c : ZMod 8, Covered 0 1 c :=
  zmod8_cases covered_0_1_0 covered_0_1_1 covered_0_1_2 covered_0_1_3
    covered_0_1_4 covered_0_1_5 covered_0_1_6 covered_0_1_7

theorem covered_0_2 : ∀ c : ZMod 8, Covered 0 2 c :=
  zmod8_cases covered_0_2_0 covered_0_2_1 covered_0_2_2 covered_0_2_3
    covered_0_2_4 covered_0_2_5 covered_0_2_6 covered_0_2_7

theorem covered_0_3 : ∀ c : ZMod 8, Covered 0 3 c :=
  zmod8_cases covered_0_3_0 covered_0_3_1 covered_0_3_2 covered_0_3_3
    covered_0_3_4 covered_0_3_5 covered_0_3_6 covered_0_3_7

theorem covered_0_4 : ∀ c : ZMod 8, Covered 0 4 c :=
  zmod8_cases covered_0_4_0 covered_0_4_1 covered_0_4_2 covered_0_4_3
    covered_0_4_4 covered_0_4_5 covered_0_4_6 covered_0_4_7

theorem covered_0_5 : ∀ c : ZMod 8, Covered 0 5 c :=
  zmod8_cases covered_0_5_0 covered_0_5_1 covered_0_5_2 covered_0_5_3
    covered_0_5_4 covered_0_5_5 covered_0_5_6 covered_0_5_7

theorem covered_0_6 : ∀ c : ZMod 8, Covered 0 6 c :=
  zmod8_cases covered_0_6_0 covered_0_6_1 covered_0_6_2 covered_0_6_3
    covered_0_6_4 covered_0_6_5 covered_0_6_6 covered_0_6_7

theorem covered_0_7 : ∀ c : ZMod 8, Covered 0 7 c :=
  zmod8_cases covered_0_7_0 covered_0_7_1 covered_0_7_2 covered_0_7_3
    covered_0_7_4 covered_0_7_5 covered_0_7_6 covered_0_7_7

theorem covered_1_0 : ∀ c : ZMod 8, Covered 1 0 c :=
  zmod8_cases covered_1_0_0 covered_1_0_1 covered_1_0_2 covered_1_0_3
    covered_1_0_4 covered_1_0_5 covered_1_0_6 covered_1_0_7

theorem covered_1_1 : ∀ c : ZMod 8, Covered 1 1 c :=
  zmod8_cases covered_1_1_0 covered_1_1_1 covered_1_1_2 covered_1_1_3
    covered_1_1_4 covered_1_1_5 covered_1_1_6 covered_1_1_7

theorem covered_1_2 : ∀ c : ZMod 8, Covered 1 2 c :=
  zmod8_cases covered_1_2_0 covered_1_2_1 covered_1_2_2 covered_1_2_3
    covered_1_2_4 covered_1_2_5 covered_1_2_6 covered_1_2_7

theorem covered_1_3 : ∀ c : ZMod 8, Covered 1 3 c :=
  zmod8_cases covered_1_3_0 covered_1_3_1 covered_1_3_2 covered_1_3_3
    covered_1_3_4 covered_1_3_5 covered_1_3_6 covered_1_3_7

theorem covered_1_4 : ∀ c : ZMod 8, Covered 1 4 c :=
  zmod8_cases covered_1_4_0 covered_1_4_1 covered_1_4_2 covered_1_4_3
    covered_1_4_4 covered_1_4_5 covered_1_4_6 covered_1_4_7

theorem covered_1_5 : ∀ c : ZMod 8, Covered 1 5 c :=
  zmod8_cases covered_1_5_0 covered_1_5_1 covered_1_5_2 covered_1_5_3
    covered_1_5_4 covered_1_5_5 covered_1_5_6 covered_1_5_7

theorem covered_1_6 : ∀ c : ZMod 8, Covered 1 6 c :=
  zmod8_cases covered_1_6_0 covered_1_6_1 covered_1_6_2 covered_1_6_3
    covered_1_6_4 covered_1_6_5 covered_1_6_6 covered_1_6_7

theorem covered_1_7 : ∀ c : ZMod 8, Covered 1 7 c :=
  zmod8_cases covered_1_7_0 covered_1_7_1 covered_1_7_2 covered_1_7_3
    covered_1_7_4 covered_1_7_5 covered_1_7_6 covered_1_7_7

theorem covered_2_0 : ∀ c : ZMod 8, Covered 2 0 c :=
  zmod8_cases covered_2_0_0 covered_2_0_1 covered_2_0_2 covered_2_0_3
    covered_2_0_4 covered_2_0_5 covered_2_0_6 covered_2_0_7

theorem covered_2_1 : ∀ c : ZMod 8, Covered 2 1 c :=
  zmod8_cases covered_2_1_0 covered_2_1_1 covered_2_1_2 covered_2_1_3
    covered_2_1_4 covered_2_1_5 covered_2_1_6 covered_2_1_7

theorem covered_2_2 : ∀ c : ZMod 8, Covered 2 2 c :=
  zmod8_cases covered_2_2_0 covered_2_2_1 covered_2_2_2 covered_2_2_3
    covered_2_2_4 covered_2_2_5 covered_2_2_6 covered_2_2_7

theorem covered_2_3 : ∀ c : ZMod 8, Covered 2 3 c :=
  zmod8_cases covered_2_3_0 covered_2_3_1 covered_2_3_2 covered_2_3_3
    covered_2_3_4 covered_2_3_5 covered_2_3_6 covered_2_3_7

theorem covered_2_4 : ∀ c : ZMod 8, Covered 2 4 c :=
  zmod8_cases covered_2_4_0 covered_2_4_1 covered_2_4_2 covered_2_4_3
    covered_2_4_4 covered_2_4_5 covered_2_4_6 covered_2_4_7

theorem covered_2_5 : ∀ c : ZMod 8, Covered 2 5 c :=
  zmod8_cases covered_2_5_0 covered_2_5_1 covered_2_5_2 covered_2_5_3
    covered_2_5_4 covered_2_5_5 covered_2_5_6 covered_2_5_7

theorem covered_2_6 : ∀ c : ZMod 8, Covered 2 6 c :=
  zmod8_cases covered_2_6_0 covered_2_6_1 covered_2_6_2 covered_2_6_3
    covered_2_6_4 covered_2_6_5 covered_2_6_6 covered_2_6_7

theorem covered_2_7 : ∀ c : ZMod 8, Covered 2 7 c :=
  zmod8_cases covered_2_7_0 covered_2_7_1 covered_2_7_2 covered_2_7_3
    covered_2_7_4 covered_2_7_5 covered_2_7_6 covered_2_7_7

theorem covered_3_0 : ∀ c : ZMod 8, Covered 3 0 c :=
  zmod8_cases covered_3_0_0 covered_3_0_1 covered_3_0_2 covered_3_0_3
    covered_3_0_4 covered_3_0_5 covered_3_0_6 covered_3_0_7

theorem covered_3_1 : ∀ c : ZMod 8, Covered 3 1 c :=
  zmod8_cases covered_3_1_0 covered_3_1_1 covered_3_1_2 covered_3_1_3
    covered_3_1_4 covered_3_1_5 covered_3_1_6 covered_3_1_7

theorem covered_3_2 : ∀ c : ZMod 8, Covered 3 2 c :=
  zmod8_cases covered_3_2_0 covered_3_2_1 covered_3_2_2 covered_3_2_3
    covered_3_2_4 covered_3_2_5 covered_3_2_6 covered_3_2_7

theorem covered_3_3 : ∀ c : ZMod 8, Covered 3 3 c :=
  zmod8_cases covered_3_3_0 covered_3_3_1 covered_3_3_2 covered_3_3_3
    covered_3_3_4 covered_3_3_5 covered_3_3_6 covered_3_3_7

theorem covered_3_4 : ∀ c : ZMod 8, Covered 3 4 c :=
  zmod8_cases covered_3_4_0 covered_3_4_1 covered_3_4_2 covered_3_4_3
    covered_3_4_4 covered_3_4_5 covered_3_4_6 covered_3_4_7

theorem covered_3_5 : ∀ c : ZMod 8, Covered 3 5 c :=
  zmod8_cases covered_3_5_0 covered_3_5_1 covered_3_5_2 covered_3_5_3
    covered_3_5_4 covered_3_5_5 covered_3_5_6 covered_3_5_7

theorem covered_3_6 : ∀ c : ZMod 8, Covered 3 6 c :=
  zmod8_cases covered_3_6_0 covered_3_6_1 covered_3_6_2 covered_3_6_3
    covered_3_6_4 covered_3_6_5 covered_3_6_6 covered_3_6_7

theorem covered_3_7 : ∀ c : ZMod 8, Covered 3 7 c :=
  zmod8_cases covered_3_7_0 covered_3_7_1 covered_3_7_2 covered_3_7_3
    covered_3_7_4 covered_3_7_5 covered_3_7_6 covered_3_7_7

theorem covered_4_0 : ∀ c : ZMod 8, Covered 4 0 c :=
  zmod8_cases covered_4_0_0 covered_4_0_1 covered_4_0_2 covered_4_0_3
    covered_4_0_4 covered_4_0_5 covered_4_0_6 covered_4_0_7

theorem covered_4_1 : ∀ c : ZMod 8, Covered 4 1 c :=
  zmod8_cases covered_4_1_0 covered_4_1_1 covered_4_1_2 covered_4_1_3
    covered_4_1_4 covered_4_1_5 covered_4_1_6 covered_4_1_7

theorem covered_4_2 : ∀ c : ZMod 8, Covered 4 2 c :=
  zmod8_cases covered_4_2_0 covered_4_2_1 covered_4_2_2 covered_4_2_3
    covered_4_2_4 covered_4_2_5 covered_4_2_6 covered_4_2_7

theorem covered_4_3 : ∀ c : ZMod 8, Covered 4 3 c :=
  zmod8_cases covered_4_3_0 covered_4_3_1 covered_4_3_2 covered_4_3_3
    covered_4_3_4 covered_4_3_5 covered_4_3_6 covered_4_3_7

theorem covered_4_4 : ∀ c : ZMod 8, Covered 4 4 c :=
  zmod8_cases covered_4_4_0 covered_4_4_1 covered_4_4_2 covered_4_4_3
    covered_4_4_4 covered_4_4_5 covered_4_4_6 covered_4_4_7

theorem covered_4_5 : ∀ c : ZMod 8, Covered 4 5 c :=
  zmod8_cases covered_4_5_0 covered_4_5_1 covered_4_5_2 covered_4_5_3
    covered_4_5_4 covered_4_5_5 covered_4_5_6 covered_4_5_7

theorem covered_4_6 : ∀ c : ZMod 8, Covered 4 6 c :=
  zmod8_cases covered_4_6_0 covered_4_6_1 covered_4_6_2 covered_4_6_3
    covered_4_6_4 covered_4_6_5 covered_4_6_6 covered_4_6_7

theorem covered_4_7 : ∀ c : ZMod 8, Covered 4 7 c :=
  zmod8_cases covered_4_7_0 covered_4_7_1 covered_4_7_2 covered_4_7_3
    covered_4_7_4 covered_4_7_5 covered_4_7_6 covered_4_7_7

theorem covered_5_0 : ∀ c : ZMod 8, Covered 5 0 c :=
  zmod8_cases covered_5_0_0 covered_5_0_1 covered_5_0_2 covered_5_0_3
    covered_5_0_4 covered_5_0_5 covered_5_0_6 covered_5_0_7

theorem covered_5_1 : ∀ c : ZMod 8, Covered 5 1 c :=
  zmod8_cases covered_5_1_0 covered_5_1_1 covered_5_1_2 covered_5_1_3
    covered_5_1_4 covered_5_1_5 covered_5_1_6 covered_5_1_7

theorem covered_5_2 : ∀ c : ZMod 8, Covered 5 2 c :=
  zmod8_cases covered_5_2_0 covered_5_2_1 covered_5_2_2 covered_5_2_3
    covered_5_2_4 covered_5_2_5 covered_5_2_6 covered_5_2_7

theorem covered_5_3 : ∀ c : ZMod 8, Covered 5 3 c :=
  zmod8_cases covered_5_3_0 covered_5_3_1 covered_5_3_2 covered_5_3_3
    covered_5_3_4 covered_5_3_5 covered_5_3_6 covered_5_3_7

theorem covered_5_4 : ∀ c : ZMod 8, Covered 5 4 c :=
  zmod8_cases covered_5_4_0 covered_5_4_1 covered_5_4_2 covered_5_4_3
    covered_5_4_4 covered_5_4_5 covered_5_4_6 covered_5_4_7

theorem covered_5_5 : ∀ c : ZMod 8, Covered 5 5 c :=
  zmod8_cases covered_5_5_0 covered_5_5_1 covered_5_5_2 covered_5_5_3
    covered_5_5_4 covered_5_5_5 covered_5_5_6 covered_5_5_7

theorem covered_5_6 : ∀ c : ZMod 8, Covered 5 6 c :=
  zmod8_cases covered_5_6_0 covered_5_6_1 covered_5_6_2 covered_5_6_3
    covered_5_6_4 covered_5_6_5 covered_5_6_6 covered_5_6_7

theorem covered_5_7 : ∀ c : ZMod 8, Covered 5 7 c :=
  zmod8_cases covered_5_7_0 covered_5_7_1 covered_5_7_2 covered_5_7_3
    covered_5_7_4 covered_5_7_5 covered_5_7_6 covered_5_7_7

theorem covered_6_0 : ∀ c : ZMod 8, Covered 6 0 c :=
  zmod8_cases covered_6_0_0 covered_6_0_1 covered_6_0_2 covered_6_0_3
    covered_6_0_4 covered_6_0_5 covered_6_0_6 covered_6_0_7

theorem covered_6_1 : ∀ c : ZMod 8, Covered 6 1 c :=
  zmod8_cases covered_6_1_0 covered_6_1_1 covered_6_1_2 covered_6_1_3
    covered_6_1_4 covered_6_1_5 covered_6_1_6 covered_6_1_7

theorem covered_6_2 : ∀ c : ZMod 8, Covered 6 2 c :=
  zmod8_cases covered_6_2_0 covered_6_2_1 covered_6_2_2 covered_6_2_3
    covered_6_2_4 covered_6_2_5 covered_6_2_6 covered_6_2_7

theorem covered_6_3 : ∀ c : ZMod 8, Covered 6 3 c :=
  zmod8_cases covered_6_3_0 covered_6_3_1 covered_6_3_2 covered_6_3_3
    covered_6_3_4 covered_6_3_5 covered_6_3_6 covered_6_3_7

theorem covered_6_4 : ∀ c : ZMod 8, Covered 6 4 c :=
  zmod8_cases covered_6_4_0 covered_6_4_1 covered_6_4_2 covered_6_4_3
    covered_6_4_4 covered_6_4_5 covered_6_4_6 covered_6_4_7

theorem covered_6_5 : ∀ c : ZMod 8, Covered 6 5 c :=
  zmod8_cases covered_6_5_0 covered_6_5_1 covered_6_5_2 covered_6_5_3
    covered_6_5_4 covered_6_5_5 covered_6_5_6 covered_6_5_7

theorem covered_6_6 : ∀ c : ZMod 8, Covered 6 6 c :=
  zmod8_cases covered_6_6_0 covered_6_6_1 covered_6_6_2 covered_6_6_3
    covered_6_6_4 covered_6_6_5 covered_6_6_6 covered_6_6_7

theorem covered_6_7 : ∀ c : ZMod 8, Covered 6 7 c :=
  zmod8_cases covered_6_7_0 covered_6_7_1 covered_6_7_2 covered_6_7_3
    covered_6_7_4 covered_6_7_5 covered_6_7_6 covered_6_7_7

theorem covered_7_0 : ∀ c : ZMod 8, Covered 7 0 c :=
  zmod8_cases covered_7_0_0 covered_7_0_1 covered_7_0_2 covered_7_0_3
    covered_7_0_4 covered_7_0_5 covered_7_0_6 covered_7_0_7

theorem covered_7_1 : ∀ c : ZMod 8, Covered 7 1 c :=
  zmod8_cases covered_7_1_0 covered_7_1_1 covered_7_1_2 covered_7_1_3
    covered_7_1_4 covered_7_1_5 covered_7_1_6 covered_7_1_7

theorem covered_7_2 : ∀ c : ZMod 8, Covered 7 2 c :=
  zmod8_cases covered_7_2_0 covered_7_2_1 covered_7_2_2 covered_7_2_3
    covered_7_2_4 covered_7_2_5 covered_7_2_6 covered_7_2_7

theorem covered_7_3 : ∀ c : ZMod 8, Covered 7 3 c :=
  zmod8_cases covered_7_3_0 covered_7_3_1 covered_7_3_2 covered_7_3_3
    covered_7_3_4 covered_7_3_5 covered_7_3_6 covered_7_3_7

theorem covered_7_4 : ∀ c : ZMod 8, Covered 7 4 c :=
  zmod8_cases covered_7_4_0 covered_7_4_1 covered_7_4_2 covered_7_4_3
    covered_7_4_4 covered_7_4_5 covered_7_4_6 covered_7_4_7

theorem covered_7_5 : ∀ c : ZMod 8, Covered 7 5 c :=
  zmod8_cases covered_7_5_0 covered_7_5_1 covered_7_5_2 covered_7_5_3
    covered_7_5_4 covered_7_5_5 covered_7_5_6 covered_7_5_7

theorem covered_7_6 : ∀ c : ZMod 8, Covered 7 6 c :=
  zmod8_cases covered_7_6_0 covered_7_6_1 covered_7_6_2 covered_7_6_3
    covered_7_6_4 covered_7_6_5 covered_7_6_6 covered_7_6_7

theorem covered_7_7 : ∀ c : ZMod 8, Covered 7 7 c :=
  zmod8_cases covered_7_7_0 covered_7_7_1 covered_7_7_2 covered_7_7_3
    covered_7_7_4 covered_7_7_5 covered_7_7_6 covered_7_7_7

/-! ### 5.2 Fixing `a`, over all `b` and `c` (8 lemmas) -/

theorem covered_0 : ∀ b c : ZMod 8, Covered 0 b c :=
  zmod8_cases covered_0_0 covered_0_1 covered_0_2 covered_0_3
    covered_0_4 covered_0_5 covered_0_6 covered_0_7

theorem covered_1 : ∀ b c : ZMod 8, Covered 1 b c :=
  zmod8_cases covered_1_0 covered_1_1 covered_1_2 covered_1_3
    covered_1_4 covered_1_5 covered_1_6 covered_1_7

theorem covered_2 : ∀ b c : ZMod 8, Covered 2 b c :=
  zmod8_cases covered_2_0 covered_2_1 covered_2_2 covered_2_3
    covered_2_4 covered_2_5 covered_2_6 covered_2_7

theorem covered_3 : ∀ b c : ZMod 8, Covered 3 b c :=
  zmod8_cases covered_3_0 covered_3_1 covered_3_2 covered_3_3
    covered_3_4 covered_3_5 covered_3_6 covered_3_7

theorem covered_4 : ∀ b c : ZMod 8, Covered 4 b c :=
  zmod8_cases covered_4_0 covered_4_1 covered_4_2 covered_4_3
    covered_4_4 covered_4_5 covered_4_6 covered_4_7

theorem covered_5 : ∀ b c : ZMod 8, Covered 5 b c :=
  zmod8_cases covered_5_0 covered_5_1 covered_5_2 covered_5_3
    covered_5_4 covered_5_5 covered_5_6 covered_5_7

theorem covered_6 : ∀ b c : ZMod 8, Covered 6 b c :=
  zmod8_cases covered_6_0 covered_6_1 covered_6_2 covered_6_3
    covered_6_4 covered_6_5 covered_6_6 covered_6_7

theorem covered_7 : ∀ b c : ZMod 8, Covered 7 b c :=
  zmod8_cases covered_7_0 covered_7_1 covered_7_2 covered_7_3
    covered_7_4 covered_7_5 covered_7_6 covered_7_7

/-! ## 6. Total coverage

The rollout obligation, discharged. -/

/-- **The rollout obligation**: every one of the 512 triples is covered. -/
def IsCovered : Prop := ∀ a b c : ZMod 8, Covered a b c

/-- **`isCovered`** — all 512 triples of `realGauge` are covered, by exhaustion
over `ZMod 8` cubed dispatching to the per-triple certificates of §4. -/
theorem isCovered : IsCovered :=
  zmod8_cases covered_0 covered_1 covered_2 covered_3 covered_4 covered_5
    covered_6 covered_7

/-! ## 7. The payoff — hypothesis-free at all 512 triples -/

/-- The hypothesis-free family. -/
noncomputable def TtabAll (hcov : IsCovered) (a b c : ZMod 8) :
    GBL realGauge a b c →ₗ[ℝ] GBR realGauge a b c :=
  Ttab (hcov a b c)

theorem TtabAll_mem (hcov : IsCovered) (a b c : ZMod 8) :
    TtabAll hcov a b c ∈ gInterSpace ℝ realGauge a b c (pTable a b c) :=
  Ttab_mem (hcov a b c)

theorem TtabAll_ne_zero (hcov : IsCovered) (a b c : ZMod 8) :
    TtabAll hcov a b c ≠ 0 :=
  Ttab_ne_zero (hcov a b c)

/-- **`hp`** — the goal of the rollout: `gParity` IS the frozen certgen table
at all 512 triples. -/
theorem hp (hcov : IsCovered) (a b c : ZMod 8) :
    gParity ℝ realGauge a b c = pTable a b c :=
  gParity_eq_pTable (hcov a b c)

/-- **`gParity_eq_pTable_all`** — `hp` instantiated at the proved `isCovered`:
the canonical parity of `realGauge` is the frozen certgen table, at every one
of the 512 triples, with no hypothesis. -/
theorem gParity_eq_pTable_all (a b c : ZMod 8) :
    gParity ℝ realGauge a b c = pTable a b c :=
  hp isCovered a b c

/-- The canonical connector exists everywhere. -/
noncomputable def TtabEverywhere (a b c : ZMod 8) :
    GBL realGauge a b c →ₗ[ℝ] GBR realGauge a b c :=
  TtabAll isCovered a b c

theorem TtabEverywhere_mem (a b c : ZMod 8) :
    TtabEverywhere a b c ∈ gInterSpace ℝ realGauge a b c (pTable a b c) :=
  TtabAll_mem isCovered a b c

theorem TtabEverywhere_ne_zero (a b c : ZMod 8) : TtabEverywhere a b c ≠ 0 :=
  TtabAll_ne_zero isCovered a b c

/-- **`connector_bridge_all`** — at every triple, generic and exceptional
alike, the tabulated data represents the semantic connector and `gParity` is
the frozen table entry. -/
theorem connector_bridge_all (a b c : ZMod 8) :
    TtabEverywhere a b c ∈ gInterSpace ℝ realGauge a b c (pTable a b c)
      ∧ TtabEverywhere a b c ≠ 0
      ∧ gParity ℝ realGauge a b c = pTable a b c :=
  connector_bridge (isCovered a b c)

end TtabAPI
end GaugeChi
end Superfusion

/-! ### Kernel self-check -/

#print axioms Superfusion.GaugeChi.TtabAPI.isCovered
#print axioms Superfusion.GaugeChi.TtabAPI.gParity_eq_pTable_all
#print axioms Superfusion.GaugeChi.TtabAPI.covered_1_4_4
#print axioms Superfusion.GaugeChi.TtabAPI.covered_1_6_1
#print axioms Superfusion.GaugeChi.TtabAPI.covered_4_4_7
#print axioms Superfusion.GaugeChi.TtabAPI.connector_bridge_all
#print axioms Superfusion.GaugeChi.TtabAPI.TtabEverywhere_ne_zero
#print axioms Superfusion.GaugeChi.TtabAPI.hp
