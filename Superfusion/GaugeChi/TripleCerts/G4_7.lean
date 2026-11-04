/-
Superfusion / GaugeChi / TripleCerts / G4_7

**GENERATED FILE — do not edit.**  Regenerate with

    python3 scripts/certgen/gen_triple_certs.py \
        --triples 4,2,7 4,3,0 4,3,1 4,3,2 4,3,4 \
        --module G4_7 \
        --out Superfusion/GaugeChi/TripleCerts/G4_7.lean

Uniform layer: `GaugeChi/RouteBridgeProto.lean` §§1–5 (the six
`route*_*Slot_coeff` bridge lemmas, `matOfCoeff_*`, `IsFuseZ`, `matGet`,
`sumPos`); arithmetic layer: `GaugeChi/CoeffChecker.lean`; assembly:
`gtOfT_mem_interSpace_of_realRepBasis` (`GaugeChi/RouteMatrixProto.lean`).
This file only instantiates them, triple by triple.

FUSION SHADOWS.  The integer shadows `fuseZ_a_b` / `hfuseZ_a_b` of the
frozen `realFuseMatrix` literals, the cast lemmas `castZ0`/`castZ1`/
`castZm1`, the packed decoder `fuseCodeZ` and the certificate consumer
`realCheckMatEq_sumPos` all live in the shared generated module
`TripleCerts/FuseShadows.lean`, which is imported below.  They are
emitted once for all 64 corners rather than re-emitted per batch: the
`fin_cases` grid that proves them dominated the elaboration of every batch,
and the duplicated shadows dominated the olean.

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
`CoeffChecker.checkMatEq_sound_submatrix`; `realCheckMatEq_sumPos` (in
`TripleCerts/FuseShadows.lean`) instantiates it and proves nothing
about the checker itself.

Only `generic` (`hsz`) triples appear here — the 12 exceptional
`(a,4,4)`/`(4,4,c)` are carried on their own track, and the split is not
visible downstream of `Ttab`.

Triples (5): (4,2,7), (4,3,0), (4,3,1), (4,3,2), (4,3,4).
Unit-slot triples (`a = 0` or `b = 0` or `c = 0`) in this batch: (4,3,0).
All of them have the IDENTITY connector in the transported frame
(measured over all 169), parity `0`, and both permutations trivial —
so their certificates carry the sign `+1` and need no matrix literal
beyond the identity array.  (Their composite frames are NOT all `1|0`.)

No `sorry`, no `native_decide`, no new axioms.
-/
import Superfusion.GaugeChi.RouteBridgeProto
import Superfusion.GaugeChi.TripleCerts.FuseShadows

namespace Superfusion
namespace GaugeChi
namespace TripleCerts
namespace G4_7

open Module

/-! ### The fusion shadows this batch uses (16 of the 64)

They are declared at the enclosing `TripleCerts` namespace by
`TripleCerts/FuseShadows.lean`, so the short names below resolve
unqualified and no `open` is needed:

  `fuseZ_2_7`, `fuseZ_3_0`, `fuseZ_3_1`, `fuseZ_3_2`, `fuseZ_3_4`, `fuseZ_4_1`, `fuseZ_4_2`, `fuseZ_4_3`, `fuseZ_4_4`, `fuseZ_4_5`, `fuseZ_4_7`, `fuseZ_6_7`, `fuseZ_7_0`, `fuseZ_7_1`, `fuseZ_7_2`, `fuseZ_7_4`. -/

/-! ### The triple `(4,2,7)`

`gaugeSizeL = gaugeSizeR = (1,1)`, `dim D_5 = 8`, certgen parity `1`; the transported connector literal. -/
section Triple_4_2_7
open Module
theorem hsz4_2_7 : realGauge.gaugeSizeR 4 2 7 = realGauge.gaugeSizeL 4 2 7 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`2 x 2 x 8`). -/
def TL4_2_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 1, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0]]]

/-- The same literal read at the composite frame `Fin 1 ⊕ Fin 1`. -/
noncomputable def Tc4_2_7 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun r s g => coeffGet TL4_2_7 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_5`. -/
noncomputable def T4_2_7 : ((realGauge.D ((4 : ZMod 8) + 2 + 7)).matrixSuper
    (realGauge.gaugeSizeL 4 2 7).1 (realGauge.gaugeSizeL 4 2 7).2).carrier :=
  matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Tc4_2_7

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT4_2_7 : T4_2_7 ∈ ((realGauge.D ((4 : ZMod 8) + 2 + 7)).matrixSuper
    (realGauge.gaugeSizeL 4 2 7).1 (realGauge.gaugeSizeL 4 2 7).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((4 : ZMod 8) + 2 + 7) Tc4_2_7 1 (by decide)

theorem T4_2_7_ne_zero : T4_2_7 ≠ 0 :=
  matOfCoeff_ne_zero ((4 : ZMod 8) + 2 + 7) Tc4_2_7 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨4, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa4_2_7_0 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 I) = (ro (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (7 : ZMod 8)).1 (realSize (2 : ZMod 8) (7 : ZMod 8)).2 (ro (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 I)
          * realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_1 (fuseRow (4 : ZMod 8) ((2 : ZMod 8) + 7) (ri (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 I) (ri (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 J) g) (fuseCol (4 : ZMod 8) ((2 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya4_2_7_0 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (lo (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) I) (lo (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_6_7 (fuseRow ((4 : ZMod 8) + 2) (7 : ZMod 8) (li (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) I) (li (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 2) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa4_2_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa4_2_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca4_2_7_0 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa4_2_7_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_2_7_0 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa4_2_7_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_2_7_0 : ∀ I J g, Xa4_2_7_0 I J g = Xca4_2_7_0 I J g := by
  decide +kernel

theorem hYtaba4_2_7_0 : ∀ I J g, Ya4_2_7_0 I J g = Yca4_2_7_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta4_2_7_0 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_2_7
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_2_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Xa4_2_7_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 hfuseZ_4_1 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Xca4_2_7_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2)) (realRepBasis ((4 : ZMod 8) + 2 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_2_7_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Ya4_2_7_0 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hfuseZ_4_2 hfuseZ_6_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Yca4_2_7_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2)) (realRepBasis ((4 : ZMod 8) + 2 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_2_7_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 2 + 7) (realGauge.gaugeSizeL 4 2 7).1 (realGauge.gaugeSizeL 4 2 7).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa4_2_7_0 TL4_2_7 YLa4_2_7_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa4_2_7_1 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 I) = (ro (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (7 : ZMod 8)).1 (realSize (2 : ZMod 8) (7 : ZMod 8)).2 (ro (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 I)
          * realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_1 (fuseRow (4 : ZMod 8) ((2 : ZMod 8) + 7) (ri (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 I) (ri (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 J) g) (fuseCol (4 : ZMod 8) ((2 : ZMod 8) + 7) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya4_2_7_1 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (lo (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) I) (lo (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_6_7 (fuseRow ((4 : ZMod 8) + 2) (7 : ZMod 8) (li (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) I) (li (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 2) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa4_2_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa4_2_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]]]

noncomputable def Xca4_2_7_1 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa4_2_7_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_2_7_1 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa4_2_7_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_2_7_1 : ∀ I J g, Xa4_2_7_1 I J g = Xca4_2_7_1 I J g := by
  decide +kernel

theorem hYtaba4_2_7_1 : ∀ I J g, Ya4_2_7_1 I J g = Yca4_2_7_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta4_2_7_1 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_2_7
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_2_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Xa4_2_7_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 hfuseZ_4_1 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Xca4_2_7_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2)) (realRepBasis ((4 : ZMod 8) + 2 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_2_7_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Ya4_2_7_1 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hfuseZ_4_2 hfuseZ_6_7 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Yca4_2_7_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2)) (realRepBasis ((4 : ZMod 8) + 2 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_2_7_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 2 + 7) (realGauge.gaugeSizeL 4 2 7).1 (realGauge.gaugeSizeL 4 2 7).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa4_2_7_1 TL4_2_7 YLa4_2_7_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa4_2_7_2 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 I) = (ro (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (7 : ZMod 8)).1 (realSize (2 : ZMod 8) (7 : ZMod 8)).2 (ro (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 I)
          * realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_1 (fuseRow (4 : ZMod 8) ((2 : ZMod 8) + 7) (ri (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 I) (ri (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 J) g) (fuseCol (4 : ZMod 8) ((2 : ZMod 8) + 7) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya4_2_7_2 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (lo (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) I) (lo (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_6_7 (fuseRow ((4 : ZMod 8) + 2) (7 : ZMod 8) (li (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) I) (li (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 2) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa4_2_7_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa4_2_7_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0]],
   [[0, 0, -1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca4_2_7_2 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa4_2_7_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_2_7_2 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa4_2_7_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_2_7_2 : ∀ I J g, Xa4_2_7_2 I J g = Xca4_2_7_2 I J g := by
  decide +kernel

theorem hYtaba4_2_7_2 : ∀ I J g, Ya4_2_7_2 I J g = Yca4_2_7_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta4_2_7_2 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_2_7
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_2_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Xa4_2_7_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 hfuseZ_4_1 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Xca4_2_7_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2)) (realRepBasis ((4 : ZMod 8) + 2 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_2_7_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Ya4_2_7_2 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hfuseZ_4_2 hfuseZ_6_7 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Yca4_2_7_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2)) (realRepBasis ((4 : ZMod 8) + 2 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_2_7_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 2 + 7) (realGauge.gaugeSizeL 4 2 7).1 (realGauge.gaugeSizeL 4 2 7).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa4_2_7_2 TL4_2_7 YLa4_2_7_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa4_2_7_3 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 I) = (ro (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (7 : ZMod 8)).1 (realSize (2 : ZMod 8) (7 : ZMod 8)).2 (ro (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 I)
          * realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_1 (fuseRow (4 : ZMod 8) ((2 : ZMod 8) + 7) (ri (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 I) (ri (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 J) g) (fuseCol (4 : ZMod 8) ((2 : ZMod 8) + 7) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya4_2_7_3 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (lo (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) I) (lo (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_6_7 (fuseRow ((4 : ZMod 8) + 2) (7 : ZMod 8) (li (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) I) (li (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 2) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa4_2_7_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa4_2_7_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0]],
   [[0, -1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca4_2_7_3 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa4_2_7_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_2_7_3 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa4_2_7_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_2_7_3 : ∀ I J g, Xa4_2_7_3 I J g = Xca4_2_7_3 I J g := by
  decide +kernel

theorem hYtaba4_2_7_3 : ∀ I J g, Ya4_2_7_3 I J g = Yca4_2_7_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta4_2_7_3 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_2_7
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_2_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Xa4_2_7_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 hfuseZ_4_1 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Xca4_2_7_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2)) (realRepBasis ((4 : ZMod 8) + 2 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_2_7_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Ya4_2_7_3 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hfuseZ_4_2 hfuseZ_6_7 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Yca4_2_7_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2)) (realRepBasis ((4 : ZMod 8) + 2 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_2_7_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 2 + 7) (realGauge.gaugeSizeL 4 2 7).1 (realGauge.gaugeSizeL 4 2 7).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa4_2_7_3 TL4_2_7 YLa4_2_7_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb4_2_7_0 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_7 (fuseRow (2 : ZMod 8) (7 : ZMod 8) (ro (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 I) (ro (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 J) ee) (fuseCol (2 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow (4 : ZMod 8) ((2 : ZMod 8) + 7) (ri (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 I) (ri (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 J) g) (fuseCol (4 : ZMod 8) ((2 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb4_2_7_0 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (lo (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) I) (lo (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_6_7 (fuseRow ((4 : ZMod 8) + 2) (7 : ZMod 8) (li (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) I) (li (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 2) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb4_2_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb4_2_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb4_2_7_0 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb4_2_7_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_2_7_0 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb4_2_7_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_2_7_0 : ∀ I J g, Xb4_2_7_0 I J g = Xcb4_2_7_0 I J g := by
  decide +kernel

theorem hYtabb4_2_7_0 : ∀ I J g, Yb4_2_7_0 I J g = Ycb4_2_7_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb4_2_7_0 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T4_2_7
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_2_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Xb4_2_7_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 hfuseZ_2_7 hfuseZ_4_1 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Xcb4_2_7_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2)) (realRepBasis ((4 : ZMod 8) + 2 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_2_7_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Yb4_2_7_0 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hfuseZ_4_2 hfuseZ_6_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Ycb4_2_7_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2)) (realRepBasis ((4 : ZMod 8) + 2 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_2_7_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 2 + 7) (realGauge.gaugeSizeL 4 2 7).1 (realGauge.gaugeSizeL 4 2 7).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_2_7_0 TL4_2_7 YLb4_2_7_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb4_2_7_1 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_7 (fuseRow (2 : ZMod 8) (7 : ZMod 8) (ro (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 I) (ro (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 J) ee) (fuseCol (2 : ZMod 8) (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow (4 : ZMod 8) ((2 : ZMod 8) + 7) (ri (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 I) (ri (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 J) g) (fuseCol (4 : ZMod 8) ((2 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb4_2_7_1 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (lo (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) I) (lo (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_6_7 (fuseRow ((4 : ZMod 8) + 2) (7 : ZMod 8) (li (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) I) (li (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 2) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb4_2_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb4_2_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]],
   [[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb4_2_7_1 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb4_2_7_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_2_7_1 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb4_2_7_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_2_7_1 : ∀ I J g, Xb4_2_7_1 I J g = Xcb4_2_7_1 I J g := by
  decide +kernel

theorem hYtabb4_2_7_1 : ∀ I J g, Yb4_2_7_1 I J g = Ycb4_2_7_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintb4_2_7_1 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T4_2_7
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_2_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Xb4_2_7_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 hfuseZ_2_7 hfuseZ_4_1 (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Xcb4_2_7_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2)) (realRepBasis ((4 : ZMod 8) + 2 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_2_7_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Yb4_2_7_1 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hfuseZ_4_2 hfuseZ_6_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Ycb4_2_7_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2)) (realRepBasis ((4 : ZMod 8) + 2 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_2_7_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 2 + 7) (realGauge.gaugeSizeL 4 2 7).1 (realGauge.gaugeSizeL 4 2 7).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_2_7_1 TL4_2_7 YLb4_2_7_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb4_2_7_2 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_7 (fuseRow (2 : ZMod 8) (7 : ZMod 8) (ro (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 I) (ro (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 J) ee) (fuseCol (2 : ZMod 8) (7 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow (4 : ZMod 8) ((2 : ZMod 8) + 7) (ri (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 I) (ri (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 J) g) (fuseCol (4 : ZMod 8) ((2 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb4_2_7_2 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (lo (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) I) (lo (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_6_7 (fuseRow ((4 : ZMod 8) + 2) (7 : ZMod 8) (li (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) I) (li (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 2) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb4_2_7_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb4_2_7_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb4_2_7_2 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb4_2_7_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_2_7_2 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb4_2_7_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_2_7_2 : ∀ I J g, Xb4_2_7_2 I J g = Xcb4_2_7_2 I J g := by
  decide +kernel

theorem hYtabb4_2_7_2 : ∀ I J g, Yb4_2_7_2 I J g = Ycb4_2_7_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintb4_2_7_2 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T4_2_7
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_2_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Xb4_2_7_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 hfuseZ_2_7 hfuseZ_4_1 (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Xcb4_2_7_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2)) (realRepBasis ((4 : ZMod 8) + 2 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_2_7_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Yb4_2_7_2 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hfuseZ_4_2 hfuseZ_6_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Ycb4_2_7_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2)) (realRepBasis ((4 : ZMod 8) + 2 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_2_7_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 2 + 7) (realGauge.gaugeSizeL 4 2 7).1 (realGauge.gaugeSizeL 4 2 7).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_2_7_2 TL4_2_7 YLb4_2_7_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb4_2_7_3 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_7 (fuseRow (2 : ZMod 8) (7 : ZMod 8) (ro (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 I) (ro (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 J) ee) (fuseCol (2 : ZMod 8) (7 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow (4 : ZMod 8) ((2 : ZMod 8) + 7) (ri (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 I) (ri (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 J) g) (fuseCol (4 : ZMod 8) ((2 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb4_2_7_3 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (lo (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) I) (lo (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_6_7 (fuseRow ((4 : ZMod 8) + 2) (7 : ZMod 8) (li (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) I) (li (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 2) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb4_2_7_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1]],
   [[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb4_2_7_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]]]

noncomputable def Xcb4_2_7_3 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb4_2_7_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_2_7_3 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb4_2_7_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_2_7_3 : ∀ I J g, Xb4_2_7_3 I J g = Xcb4_2_7_3 I J g := by
  decide +kernel

theorem hYtabb4_2_7_3 : ∀ I J g, Yb4_2_7_3 I J g = Ycb4_2_7_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb4_2_7_3 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T4_2_7
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_2_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Xb4_2_7_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 hfuseZ_2_7 hfuseZ_4_1 (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Xcb4_2_7_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2)) (realRepBasis ((4 : ZMod 8) + 2 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_2_7_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Yb4_2_7_3 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hfuseZ_4_2 hfuseZ_6_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Ycb4_2_7_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2)) (realRepBasis ((4 : ZMod 8) + 2 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_2_7_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 2 + 7) (realGauge.gaugeSizeL 4 2 7).1 (realGauge.gaugeSizeL 4 2 7).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_2_7_3 TL4_2_7 YLb4_2_7_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc4_2_7_0 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_7 (fuseRow (2 : ZMod 8) (7 : ZMod 8) (ro (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 I) (ro (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 J) ee) (fuseCol (2 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow (4 : ZMod 8) ((2 : ZMod 8) + 7) (ri (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 I) (ri (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 J) g) (fuseCol (4 : ZMod 8) ((2 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc4_2_7_0 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun I J g => if (lo (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) I) = (lo (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (2 : ZMod 8)).1 (realSize (4 : ZMod 8) (2 : ZMod 8)).2 (lo (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) I)
          * realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_7 (fuseRow ((4 : ZMod 8) + 2) (7 : ZMod 8) (li (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) I) (li (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 2) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc4_2_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc4_2_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcc4_2_7_0 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun r s g => coeffGet XLc4_2_7_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc4_2_7_0 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun r s g => coeffGet YLc4_2_7_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc4_2_7_0 : ∀ I J g, Xc4_2_7_0 I J g = Xcc4_2_7_0 I J g := by
  decide +kernel

theorem hYtabc4_2_7_0 : ∀ I J g, Yc4_2_7_0 I J g = Ycc4_2_7_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc4_2_7_0 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T4_2_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_2_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Xc4_2_7_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 hfuseZ_2_7 hfuseZ_4_1 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Xcc4_2_7_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2)) (realRepBasis ((4 : ZMod 8) + 2 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabc4_2_7_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Yc4_2_7_0 := Matrix.ext fun I J => routeL_cSlot_coeff (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hfuseZ_6_7 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Ycc4_2_7_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2)) (realRepBasis ((4 : ZMod 8) + 2 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabc4_2_7_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 2 + 7) (realGauge.gaugeSizeL 4 2 7).1 (realGauge.gaugeSizeL 4 2 7).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc4_2_7_0 TL4_2_7 YLc4_2_7_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc4_2_7_1 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_7 (fuseRow (2 : ZMod 8) (7 : ZMod 8) (ro (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 I) (ro (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 J) ee) (fuseCol (2 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow (4 : ZMod 8) ((2 : ZMod 8) + 7) (ri (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 I) (ri (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 J) g) (fuseCol (4 : ZMod 8) ((2 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc4_2_7_1 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun I J g => if (lo (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) I) = (lo (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (2 : ZMod 8)).1 (realSize (4 : ZMod 8) (2 : ZMod 8)).2 (lo (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) I)
          * realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_7 (fuseRow ((4 : ZMod 8) + 2) (7 : ZMod 8) (li (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) I) (li (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 2) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc4_2_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc4_2_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0]]]

noncomputable def Xcc4_2_7_1 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun r s g => coeffGet XLc4_2_7_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc4_2_7_1 : (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2) → Fin (realRepDim ((4 : ZMod 8) + 2 + 7).val) → ℤ :=
  fun r s g => coeffGet YLc4_2_7_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc4_2_7_1 : ∀ I J g, Xc4_2_7_1 I J g = Xcc4_2_7_1 I J g := by
  decide +kernel

theorem hYtabc4_2_7_1 : ∀ I J g, Yc4_2_7_1 I J g = Ycc4_2_7_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintc4_2_7_1 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T4_2_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_2_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Xc4_2_7_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 hfuseZ_2_7 hfuseZ_4_1 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Xcc4_2_7_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2)) (realRepBasis ((4 : ZMod 8) + 2 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabc4_2_7_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Yc4_2_7_1 := Matrix.ext fun I J => routeL_cSlot_coeff (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hfuseZ_6_7 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 2 + 7)) Ycc4_2_7_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 2 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 2 7).2)) (realRepBasis ((4 : ZMod 8) + 2 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabc4_2_7_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 2 + 7) (realGauge.gaugeSizeL 4 2 7).1 (realGauge.gaugeSizeL 4 2 7).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc4_2_7_1 TL4_2_7 YLc4_2_7_1 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint4_2_7 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T4_2_7
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T4_2_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hinta4_2_7_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hinta4_2_7_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hinta4_2_7_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hinta4_2_7_3

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint4_2_7 (i : Fin (realRepDim (2 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) i)) * T4_2_7
      = ((sgn (realRepBasisParity (2 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T4_2_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h0]; exact hintb4_2_7_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h1]; exact hintb4_2_7_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h2]; exact hintb4_2_7_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h3]; exact hintb4_2_7_3

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint4_2_7 (i : Fin (realRepDim (7 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) i)) * T4_2_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T4_2_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h0]; exact hintc4_2_7_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h1]; exact hintc4_2_7_1

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT4_2_7_mem_gInterSpace :
    gtOfT ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 T4_2_7 ∈ gInterSpace ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 hT4_2_7 hAint4_2_7 hBint4_2_7 hCint4_2_7

theorem gtOfT4_2_7_ne_zero : gtOfT ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 T4_2_7 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) hsz4_2_7 T4_2_7_ne_zero

theorem gInterSpace4_2_7_ne_bot : gInterSpace ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT4_2_7_mem_gInterSpace, gtOfT4_2_7_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_4_2_7 : gParity ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (4 : ZMod 8) (2 : ZMod 8) (7 : ZMod 8) gInterSpace4_2_7_ne_bot).symm

end Triple_4_2_7

/-! ### The triple `(4,3,0)`

`gaugeSizeL = gaugeSizeR = (2,2)`, `dim D_7 = 2`, certgen parity `0`; the unit-slot shortcut: the connector is the identity, so every certificate carries the sign `+1`. -/
section Triple_4_3_0
open Module
theorem hsz4_3_0 : realGauge.gaugeSizeR 4 3 0 = realGauge.gaugeSizeL 4 3 0 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`4 x 4 x 2`). -/
def TL4_3_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

/-- The same literal read at the composite frame `Fin 2 ⊕ Fin 2`. -/
noncomputable def Tc4_3_0 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun r s g => coeffGet TL4_3_0 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_7`. -/
noncomputable def T4_3_0 : ((realGauge.D ((4 : ZMod 8) + 3 + 0)).matrixSuper
    (realGauge.gaugeSizeL 4 3 0).1 (realGauge.gaugeSizeL 4 3 0).2).carrier :=
  matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Tc4_3_0

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT4_3_0 : T4_3_0 ∈ ((realGauge.D ((4 : ZMod 8) + 3 + 0)).matrixSuper
    (realGauge.gaugeSizeL 4 3 0).1 (realGauge.gaugeSizeL 4 3 0).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((4 : ZMod 8) + 3 + 0) Tc4_3_0 0 (by decide)

theorem T4_3_0_ne_zero : T4_3_0 ≠ 0 :=
  matOfCoeff_ne_zero ((4 : ZMod 8) + 3 + 0) Tc4_3_0 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa4_3_0_0 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I) = (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (0 : ZMod 8)).1 (realSize (3 : ZMod 8) (0 : ZMod 8)).2 (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I)
          * realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 0) (ri (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I) (ri (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya4_3_0_0 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_0 (fuseRow ((4 : ZMod 8) + 3) (0 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa4_3_0_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa4_3_0_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xca4_3_0_0 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa4_3_0_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_3_0_0 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa4_3_0_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_3_0_0 : ∀ I J g, Xa4_3_0_0 I J g = Xca4_3_0_0 I J g := by
  decide +kernel

theorem hYtaba4_3_0_0 : ∀ I J g, Ya4_3_0_0 I J g = Yca4_3_0_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta4_3_0_0 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_3_0
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_0 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Xa4_3_0_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Xca4_3_0_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2)) (realRepBasis ((4 : ZMod 8) + 3 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_3_0_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Ya4_3_0_0 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hfuseZ_4_3 hfuseZ_7_0 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Yca4_3_0_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2)) (realRepBasis ((4 : ZMod 8) + 3 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_3_0_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 0) (realGauge.gaugeSizeL 4 3 0).1 (realGauge.gaugeSizeL 4 3 0).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa4_3_0_0 TL4_3_0 YLa4_3_0_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa4_3_0_1 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I) = (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (0 : ZMod 8)).1 (realSize (3 : ZMod 8) (0 : ZMod 8)).2 (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I)
          * realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 0) (ri (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I) (ri (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 0) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya4_3_0_1 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_0 (fuseRow ((4 : ZMod 8) + 3) (0 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa4_3_0_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa4_3_0_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]]]

noncomputable def Xca4_3_0_1 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa4_3_0_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_3_0_1 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa4_3_0_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_3_0_1 : ∀ I J g, Xa4_3_0_1 I J g = Xca4_3_0_1 I J g := by
  decide +kernel

theorem hYtaba4_3_0_1 : ∀ I J g, Ya4_3_0_1 I J g = Yca4_3_0_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta4_3_0_1 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_3_0
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_0 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Xa4_3_0_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 hfuseZ_4_3 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Xca4_3_0_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2)) (realRepBasis ((4 : ZMod 8) + 3 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_3_0_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Ya4_3_0_1 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hfuseZ_4_3 hfuseZ_7_0 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Yca4_3_0_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2)) (realRepBasis ((4 : ZMod 8) + 3 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_3_0_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 0) (realGauge.gaugeSizeL 4 3 0).1 (realGauge.gaugeSizeL 4 3 0).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa4_3_0_1 TL4_3_0 YLa4_3_0_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa4_3_0_2 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I) = (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (0 : ZMod 8)).1 (realSize (3 : ZMod 8) (0 : ZMod 8)).2 (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I)
          * realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 0) (ri (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I) (ri (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 0) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya4_3_0_2 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_0 (fuseRow ((4 : ZMod 8) + 3) (0 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa4_3_0_2 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa4_3_0_2 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0]]]

noncomputable def Xca4_3_0_2 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa4_3_0_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_3_0_2 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa4_3_0_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_3_0_2 : ∀ I J g, Xa4_3_0_2 I J g = Xca4_3_0_2 I J g := by
  decide +kernel

theorem hYtaba4_3_0_2 : ∀ I J g, Ya4_3_0_2 I J g = Yca4_3_0_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta4_3_0_2 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_3_0
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_0 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Xa4_3_0_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 hfuseZ_4_3 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Xca4_3_0_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2)) (realRepBasis ((4 : ZMod 8) + 3 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_3_0_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Ya4_3_0_2 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hfuseZ_4_3 hfuseZ_7_0 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Yca4_3_0_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2)) (realRepBasis ((4 : ZMod 8) + 3 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_3_0_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 0) (realGauge.gaugeSizeL 4 3 0).1 (realGauge.gaugeSizeL 4 3 0).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa4_3_0_2 TL4_3_0 YLa4_3_0_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa4_3_0_3 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I) = (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (0 : ZMod 8)).1 (realSize (3 : ZMod 8) (0 : ZMod 8)).2 (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I)
          * realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 0) (ri (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I) (ri (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 0) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya4_3_0_3 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_0 (fuseRow ((4 : ZMod 8) + 3) (0 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa4_3_0_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa4_3_0_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca4_3_0_3 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa4_3_0_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_3_0_3 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa4_3_0_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_3_0_3 : ∀ I J g, Xa4_3_0_3 I J g = Xca4_3_0_3 I J g := by
  decide +kernel

theorem hYtaba4_3_0_3 : ∀ I J g, Ya4_3_0_3 I J g = Yca4_3_0_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta4_3_0_3 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_3_0
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_0 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Xa4_3_0_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 hfuseZ_4_3 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Xca4_3_0_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2)) (realRepBasis ((4 : ZMod 8) + 3 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_3_0_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Ya4_3_0_3 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hfuseZ_4_3 hfuseZ_7_0 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Yca4_3_0_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2)) (realRepBasis ((4 : ZMod 8) + 3 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_3_0_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 0) (realGauge.gaugeSizeL 4 3 0).1 (realGauge.gaugeSizeL 4 3 0).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa4_3_0_3 TL4_3_0 YLa4_3_0_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb4_3_0_0 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_0 (fuseRow (3 : ZMod 8) (0 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I) (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 J) ee) (fuseCol (3 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 0) (ri (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I) (ri (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb4_3_0_0 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_0 (fuseRow ((4 : ZMod 8) + 3) (0 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb4_3_0_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb4_3_0_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcb4_3_0_0 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_0_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_0_0 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_0_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_0_0 : ∀ I J g, Xb4_3_0_0 I J g = Xcb4_3_0_0 I J g := by
  decide +kernel

theorem hYtabb4_3_0_0 : ∀ I J g, Yb4_3_0_0 I J g = Ycb4_3_0_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb4_3_0_0 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_0
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_0 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Xb4_3_0_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 hfuseZ_3_0 hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Xcb4_3_0_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2)) (realRepBasis ((4 : ZMod 8) + 3 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_0_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Yb4_3_0_0 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hfuseZ_4_3 hfuseZ_7_0 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Ycb4_3_0_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2)) (realRepBasis ((4 : ZMod 8) + 3 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_0_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 0) (realGauge.gaugeSizeL 4 3 0).1 (realGauge.gaugeSizeL 4 3 0).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_3_0_0 TL4_3_0 YLb4_3_0_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb4_3_0_1 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_0 (fuseRow (3 : ZMod 8) (0 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I) (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 J) ee) (fuseCol (3 : ZMod 8) (0 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 0) (ri (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I) (ri (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb4_3_0_1 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_0 (fuseRow ((4 : ZMod 8) + 3) (0 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb4_3_0_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 1], [0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb4_3_0_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 1], [0, 0]]]

noncomputable def Xcb4_3_0_1 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_0_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_0_1 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_0_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_0_1 : ∀ I J g, Xb4_3_0_1 I J g = Xcb4_3_0_1 I J g := by
  decide +kernel

theorem hYtabb4_3_0_1 : ∀ I J g, Yb4_3_0_1 I J g = Ycb4_3_0_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb4_3_0_1 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_0
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_0 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Xb4_3_0_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 hfuseZ_3_0 hfuseZ_4_3 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Xcb4_3_0_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2)) (realRepBasis ((4 : ZMod 8) + 3 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_0_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Yb4_3_0_1 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hfuseZ_4_3 hfuseZ_7_0 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Ycb4_3_0_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2)) (realRepBasis ((4 : ZMod 8) + 3 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_0_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 0) (realGauge.gaugeSizeL 4 3 0).1 (realGauge.gaugeSizeL 4 3 0).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_3_0_1 TL4_3_0 YLb4_3_0_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb4_3_0_2 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_0 (fuseRow (3 : ZMod 8) (0 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I) (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 J) ee) (fuseCol (3 : ZMod 8) (0 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 0) (ri (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I) (ri (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb4_3_0_2 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_0 (fuseRow ((4 : ZMod 8) + 3) (0 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb4_3_0_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb4_3_0_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb4_3_0_2 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_0_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_0_2 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_0_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_0_2 : ∀ I J g, Xb4_3_0_2 I J g = Xcb4_3_0_2 I J g := by
  decide +kernel

theorem hYtabb4_3_0_2 : ∀ I J g, Yb4_3_0_2 I J g = Ycb4_3_0_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb4_3_0_2 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_0
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_0 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Xb4_3_0_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 hfuseZ_3_0 hfuseZ_4_3 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Xcb4_3_0_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2)) (realRepBasis ((4 : ZMod 8) + 3 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_0_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Yb4_3_0_2 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hfuseZ_4_3 hfuseZ_7_0 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Ycb4_3_0_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2)) (realRepBasis ((4 : ZMod 8) + 3 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_0_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 0) (realGauge.gaugeSizeL 4 3 0).1 (realGauge.gaugeSizeL 4 3 0).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_3_0_2 TL4_3_0 YLb4_3_0_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb4_3_0_3 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_0 (fuseRow (3 : ZMod 8) (0 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I) (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 J) ee) (fuseCol (3 : ZMod 8) (0 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 0) (ri (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I) (ri (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb4_3_0_3 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_0 (fuseRow ((4 : ZMod 8) + 3) (0 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb4_3_0_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb4_3_0_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]]]

noncomputable def Xcb4_3_0_3 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_0_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_0_3 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_0_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_0_3 : ∀ I J g, Xb4_3_0_3 I J g = Xcb4_3_0_3 I J g := by
  decide +kernel

theorem hYtabb4_3_0_3 : ∀ I J g, Yb4_3_0_3 I J g = Ycb4_3_0_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb4_3_0_3 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_0
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_0 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Xb4_3_0_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 hfuseZ_3_0 hfuseZ_4_3 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Xcb4_3_0_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2)) (realRepBasis ((4 : ZMod 8) + 3 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_0_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Yb4_3_0_3 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hfuseZ_4_3 hfuseZ_7_0 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Ycb4_3_0_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2)) (realRepBasis ((4 : ZMod 8) + 3 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_0_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 0) (realGauge.gaugeSizeL 4 3 0).1 (realGauge.gaugeSizeL 4 3 0).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_3_0_3 TL4_3_0 YLb4_3_0_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Xb4_3_0_4 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_0 (fuseRow (3 : ZMod 8) (0 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I) (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 J) ee) (fuseCol (3 : ZMod 8) (0 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 0) (ri (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I) (ri (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Yb4_3_0_4 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_0 (fuseRow ((4 : ZMod 8) + 3) (0 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `4`, pre-tabulated. -/
def XLb4_3_0_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `4`, pre-tabulated. -/
def YLb4_3_0_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0]]]

noncomputable def Xcb4_3_0_4 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_0_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_0_4 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_0_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_0_4 : ∀ I J g, Xb4_3_0_4 I J g = Xcb4_3_0_4 I J g := by
  decide +kernel

theorem hYtabb4_3_0_4 : ∀ I J g, Yb4_3_0_4 I J g = Ycb4_3_0_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `4`** (Koszul sign `+1`). -/
theorem hintb4_3_0_4 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_0
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_0 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Xb4_3_0_4 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 hfuseZ_3_0 hfuseZ_4_3 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Xcb4_3_0_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2)) (realRepBasis ((4 : ZMod 8) + 3 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_0_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Yb4_3_0_4 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hfuseZ_4_3 hfuseZ_7_0 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Ycb4_3_0_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2)) (realRepBasis ((4 : ZMod 8) + 3 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_0_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 0) (realGauge.gaugeSizeL 4 3 0).1 (realGauge.gaugeSizeL 4 3 0).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_3_0_4 TL4_3_0 YLb4_3_0_4 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Xb4_3_0_5 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_0 (fuseRow (3 : ZMod 8) (0 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I) (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 J) ee) (fuseCol (3 : ZMod 8) (0 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 0) (ri (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I) (ri (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Yb4_3_0_5 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_0 (fuseRow ((4 : ZMod 8) + 3) (0 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `5`, pre-tabulated. -/
def XLb4_3_0_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `5`, pre-tabulated. -/
def YLb4_3_0_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb4_3_0_5 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_0_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_0_5 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_0_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_0_5 : ∀ I J g, Xb4_3_0_5 I J g = Xcb4_3_0_5 I J g := by
  decide +kernel

theorem hYtabb4_3_0_5 : ∀ I J g, Yb4_3_0_5 I J g = Ycb4_3_0_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintb4_3_0_5 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_0
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_0 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Xb4_3_0_5 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 hfuseZ_3_0 hfuseZ_4_3 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Xcb4_3_0_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2)) (realRepBasis ((4 : ZMod 8) + 3 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_0_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Yb4_3_0_5 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hfuseZ_4_3 hfuseZ_7_0 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Ycb4_3_0_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2)) (realRepBasis ((4 : ZMod 8) + 3 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_0_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 0) (realGauge.gaugeSizeL 4 3 0).1 (realGauge.gaugeSizeL 4 3 0).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_3_0_5 TL4_3_0 YLb4_3_0_5 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Xb4_3_0_6 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_0 (fuseRow (3 : ZMod 8) (0 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I) (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 J) ee) (fuseCol (3 : ZMod 8) (0 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 0) (ri (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I) (ri (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Yb4_3_0_6 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_0 (fuseRow ((4 : ZMod 8) + 3) (0 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `6`, pre-tabulated. -/
def XLb4_3_0_6 : List (List (List ℤ)) :=
  [[[0, 0], [-1, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `6`, pre-tabulated. -/
def YLb4_3_0_6 : List (List (List ℤ)) :=
  [[[0, 0], [-1, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0]]]

noncomputable def Xcb4_3_0_6 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_0_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_0_6 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_0_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_0_6 : ∀ I J g, Xb4_3_0_6 I J g = Xcb4_3_0_6 I J g := by
  decide +kernel

theorem hYtabb4_3_0_6 : ∀ I J g, Yb4_3_0_6 I J g = Ycb4_3_0_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintb4_3_0_6 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_0
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_0 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Xb4_3_0_6 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 hfuseZ_3_0 hfuseZ_4_3 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Xcb4_3_0_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2)) (realRepBasis ((4 : ZMod 8) + 3 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_0_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Yb4_3_0_6 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hfuseZ_4_3 hfuseZ_7_0 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Ycb4_3_0_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2)) (realRepBasis ((4 : ZMod 8) + 3 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_0_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 0) (realGauge.gaugeSizeL 4 3 0).1 (realGauge.gaugeSizeL 4 3 0).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_3_0_6 TL4_3_0 YLb4_3_0_6 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Xb4_3_0_7 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_0 (fuseRow (3 : ZMod 8) (0 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I) (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 J) ee) (fuseCol (3 : ZMod 8) (0 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 0) (ri (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I) (ri (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Yb4_3_0_7 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_0 (fuseRow ((4 : ZMod 8) + 3) (0 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `7`, pre-tabulated. -/
def XLb4_3_0_7 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1]]]

/-- Left route at the `b`-slot generator `7`, pre-tabulated. -/
def YLb4_3_0_7 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1]]]

noncomputable def Xcb4_3_0_7 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_0_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_0_7 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_0_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_0_7 : ∀ I J g, Xb4_3_0_7 I J g = Xcb4_3_0_7 I J g := by
  decide +kernel

theorem hYtabb4_3_0_7 : ∀ I J g, Yb4_3_0_7 I J g = Ycb4_3_0_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `7`** (Koszul sign `+1`). -/
theorem hintb4_3_0_7 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_0
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_0 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Xb4_3_0_7 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 hfuseZ_3_0 hfuseZ_4_3 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Xcb4_3_0_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2)) (realRepBasis ((4 : ZMod 8) + 3 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_0_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Yb4_3_0_7 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hfuseZ_4_3 hfuseZ_7_0 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Ycb4_3_0_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2)) (realRepBasis ((4 : ZMod 8) + 3 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_0_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 0) (realGauge.gaugeSizeL 4 3 0).1 (realGauge.gaugeSizeL 4 3 0).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_3_0_7 TL4_3_0 YLb4_3_0_7 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc4_3_0_0 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_0 (fuseRow (3 : ZMod 8) (0 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I) (ro (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 J) ee) (fuseCol (3 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 0) (ri (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 I) (ri (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc4_3_0_0 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun I J g => if (lo (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) I) = (lo (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (3 : ZMod 8)).1 (realSize (4 : ZMod 8) (3 : ZMod 8)).2 (lo (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) I)
          * realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_7_0 (fuseRow ((4 : ZMod 8) + 3) (0 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc4_3_0_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc4_3_0_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcc4_3_0_0 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun r s g => coeffGet XLc4_3_0_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc4_3_0_0 : (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 0).val) → ℤ :=
  fun r s g => coeffGet YLc4_3_0_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc4_3_0_0 : ∀ I J g, Xc4_3_0_0 I J g = Xcc4_3_0_0 I J g := by
  decide +kernel

theorem hYtabc4_3_0_0 : ∀ I J g, Yc4_3_0_0 I J g = Ycc4_3_0_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc4_3_0_0 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))) * T4_3_0
      = ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_0 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Xc4_3_0_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 hfuseZ_3_0 hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Xcc4_3_0_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2)) (realRepBasis ((4 : ZMod 8) + 3 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabc4_3_0_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Yc4_3_0_0 := Matrix.ext fun I J => routeL_cSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hfuseZ_7_0 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 0)) Ycc4_3_0_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 0).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 0).2)) (realRepBasis ((4 : ZMod 8) + 3 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabc4_3_0_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 0) (realGauge.gaugeSizeL 4 3 0).1 (realGauge.gaugeSizeL 4 3 0).2 ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc4_3_0_0 TL4_3_0 YLc4_3_0_0 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint4_3_0 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T4_3_0
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T4_3_0 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hinta4_3_0_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hinta4_3_0_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hinta4_3_0_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hinta4_3_0_3

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint4_3_0 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T4_3_0
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T4_3_0 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hintb4_3_0_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hintb4_3_0_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hintb4_3_0_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hintb4_3_0_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hintb4_3_0_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hintb4_3_0_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hintb4_3_0_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hintb4_3_0_7

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint4_3_0 (i : Fin (realRepDim (0 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) i)) * T4_3_0
      = ((sgn (realRepBasisParity (0 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T4_3_0 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 1 := i.isLt
  have h0 : (i : ℕ) = 0 := by omega
  rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) from Fin.ext h0]
  exact hintc4_3_0_0

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT4_3_0_mem_gInterSpace :
    gtOfT ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 T4_3_0 ∈ gInterSpace ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 hT4_3_0 hAint4_3_0 hBint4_3_0 hCint4_3_0

theorem gtOfT4_3_0_ne_zero : gtOfT ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 T4_3_0 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) hsz4_3_0 T4_3_0_ne_zero

theorem gInterSpace4_3_0_ne_bot : gInterSpace ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT4_3_0_mem_gInterSpace, gtOfT4_3_0_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_4_3_0 : gParity ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (0 : ZMod 8) gInterSpace4_3_0_ne_bot).symm

end Triple_4_3_0

/-! ### The triple `(4,3,1)`

`gaugeSizeL = gaugeSizeR = (4,4)`, `dim D_0 = 1`, certgen parity `1`; the transported connector literal. -/
section Triple_4_3_1
open Module
theorem hsz4_3_1 : realGauge.gaugeSizeR 4 3 1 = realGauge.gaugeSizeL 4 3 1 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`8 x 8 x 1`). -/
def TL4_3_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [1], [1], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [1]],
   [[0], [0], [0], [0], [1], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [1], [-1], [0]],
   [[1], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [1], [-1], [0], [0], [0], [0], [0]],
   [[0], [-1], [-1], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [-1], [0], [0], [0], [0]]]

/-- The same literal read at the composite frame `Fin 4 ⊕ Fin 4`. -/
noncomputable def Tc4_3_1 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet TL4_3_1 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_0`. -/
noncomputable def T4_3_1 : ((realGauge.D ((4 : ZMod 8) + 3 + 1)).matrixSuper
    (realGauge.gaugeSizeL 4 3 1).1 (realGauge.gaugeSizeL 4 3 1).2).carrier :=
  matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Tc4_3_1

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT4_3_1 : T4_3_1 ∈ ((realGauge.D ((4 : ZMod 8) + 3 + 1)).matrixSuper
    (realGauge.gaugeSizeL 4 3 1).1 (realGauge.gaugeSizeL 4 3 1).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((4 : ZMod 8) + 3 + 1) Tc4_3_1 1 (by decide)

theorem T4_3_1_ne_zero : T4_3_1 ≠ 0 :=
  matOfCoeff_ne_zero ((4 : ZMod 8) + 3 + 1) Tc4_3_1 (Sum.inl ⟨0, by decide⟩) (Sum.inr ⟨1, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa4_3_1_0 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) = (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I)
          * realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 1) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya4_3_1_0 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_1 (fuseRow ((4 : ZMod 8) + 3) (1 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa4_3_1_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa4_3_1_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xca4_3_1_0 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet XLa4_3_1_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_3_1_0 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet YLa4_3_1_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_3_1_0 : ∀ I J g, Xa4_3_1_0 I J g = Xca4_3_1_0 I J g := by
  decide +kernel

theorem hYtaba4_3_1_0 : ∀ I J g, Ya4_3_1_0 I J g = Yca4_3_1_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta4_3_1_0 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_3_1
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_1 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xa4_3_1_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xca4_3_1_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_3_1_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Ya4_3_1_0 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hfuseZ_4_3 hfuseZ_7_1 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Yca4_3_1_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_3_1_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 1) (realGauge.gaugeSizeL 4 3 1).1 (realGauge.gaugeSizeL 4 3 1).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa4_3_1_0 TL4_3_1 YLa4_3_1_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa4_3_1_1 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) = (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I)
          * realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 1) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 1) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya4_3_1_1 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_1 (fuseRow ((4 : ZMod 8) + 3) (1 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa4_3_1_1 : List (List (List ℤ)) :=
  [[[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa4_3_1_1 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]]]

noncomputable def Xca4_3_1_1 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet XLa4_3_1_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_3_1_1 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet YLa4_3_1_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_3_1_1 : ∀ I J g, Xa4_3_1_1 I J g = Xca4_3_1_1 I J g := by
  decide +kernel

theorem hYtaba4_3_1_1 : ∀ I J g, Ya4_3_1_1 I J g = Yca4_3_1_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta4_3_1_1 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_3_1
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_1 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xa4_3_1_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 hfuseZ_4_4 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xca4_3_1_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_3_1_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Ya4_3_1_1 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hfuseZ_4_3 hfuseZ_7_1 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Yca4_3_1_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_3_1_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 1) (realGauge.gaugeSizeL 4 3 1).1 (realGauge.gaugeSizeL 4 3 1).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa4_3_1_1 TL4_3_1 YLa4_3_1_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa4_3_1_2 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) = (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I)
          * realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 1) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 1) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya4_3_1_2 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_1 (fuseRow ((4 : ZMod 8) + 3) (1 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa4_3_1_2 : List (List (List ℤ)) :=
  [[[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa4_3_1_2 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

noncomputable def Xca4_3_1_2 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet XLa4_3_1_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_3_1_2 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet YLa4_3_1_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_3_1_2 : ∀ I J g, Xa4_3_1_2 I J g = Xca4_3_1_2 I J g := by
  decide +kernel

theorem hYtaba4_3_1_2 : ∀ I J g, Ya4_3_1_2 I J g = Yca4_3_1_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta4_3_1_2 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_3_1
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_1 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xa4_3_1_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 hfuseZ_4_4 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xca4_3_1_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_3_1_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Ya4_3_1_2 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hfuseZ_4_3 hfuseZ_7_1 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Yca4_3_1_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_3_1_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 1) (realGauge.gaugeSizeL 4 3 1).1 (realGauge.gaugeSizeL 4 3 1).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa4_3_1_2 TL4_3_1 YLa4_3_1_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa4_3_1_3 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) = (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I)
          * realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 1) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 1) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya4_3_1_3 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_1 (fuseRow ((4 : ZMod 8) + 3) (1 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa4_3_1_3 : List (List (List ℤ)) :=
  [[[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa4_3_1_3 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

noncomputable def Xca4_3_1_3 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet XLa4_3_1_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_3_1_3 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet YLa4_3_1_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_3_1_3 : ∀ I J g, Xa4_3_1_3 I J g = Xca4_3_1_3 I J g := by
  decide +kernel

theorem hYtaba4_3_1_3 : ∀ I J g, Ya4_3_1_3 I J g = Yca4_3_1_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta4_3_1_3 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_3_1
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_1 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xa4_3_1_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 hfuseZ_4_4 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xca4_3_1_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_3_1_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Ya4_3_1_3 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hfuseZ_4_3 hfuseZ_7_1 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Yca4_3_1_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_3_1_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 1) (realGauge.gaugeSizeL 4 3 1).1 (realGauge.gaugeSizeL 4 3 1).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa4_3_1_3 TL4_3_1 YLa4_3_1_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb4_3_1_0 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 1) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb4_3_1_0 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_1 (fuseRow ((4 : ZMod 8) + 3) (1 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb4_3_1_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb4_3_1_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xcb4_3_1_0 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_1_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_1_0 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_1_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_1_0 : ∀ I J g, Xb4_3_1_0 I J g = Xcb4_3_1_0 I J g := by
  decide +kernel

theorem hYtabb4_3_1_0 : ∀ I J g, Yb4_3_1_0 I J g = Ycb4_3_1_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb4_3_1_0 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_1
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_1 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xb4_3_1_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 hfuseZ_3_1 hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xcb4_3_1_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_1_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Yb4_3_1_0 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hfuseZ_4_3 hfuseZ_7_1 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Ycb4_3_1_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_1_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 1) (realGauge.gaugeSizeL 4 3 1).1 (realGauge.gaugeSizeL 4 3 1).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_3_1_0 TL4_3_1 YLb4_3_1_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb4_3_1_1 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 1) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb4_3_1_1 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_1 (fuseRow ((4 : ZMod 8) + 3) (1 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb4_3_1_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb4_3_1_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]]]

noncomputable def Xcb4_3_1_1 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_1_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_1_1 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_1_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_1_1 : ∀ I J g, Xb4_3_1_1 I J g = Xcb4_3_1_1 I J g := by
  decide +kernel

theorem hYtabb4_3_1_1 : ∀ I J g, Yb4_3_1_1 I J g = Ycb4_3_1_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintb4_3_1_1 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_1
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_1 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xb4_3_1_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 hfuseZ_3_1 hfuseZ_4_4 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xcb4_3_1_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_1_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Yb4_3_1_1 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hfuseZ_4_3 hfuseZ_7_1 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Ycb4_3_1_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_1_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 1) (realGauge.gaugeSizeL 4 3 1).1 (realGauge.gaugeSizeL 4 3 1).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_3_1_1 TL4_3_1 YLb4_3_1_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb4_3_1_2 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 1) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb4_3_1_2 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_1 (fuseRow ((4 : ZMod 8) + 3) (1 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb4_3_1_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb4_3_1_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xcb4_3_1_2 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_1_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_1_2 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_1_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_1_2 : ∀ I J g, Xb4_3_1_2 I J g = Xcb4_3_1_2 I J g := by
  decide +kernel

theorem hYtabb4_3_1_2 : ∀ I J g, Yb4_3_1_2 I J g = Ycb4_3_1_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintb4_3_1_2 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_1
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_1 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xb4_3_1_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 hfuseZ_3_1 hfuseZ_4_4 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xcb4_3_1_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_1_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Yb4_3_1_2 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hfuseZ_4_3 hfuseZ_7_1 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Ycb4_3_1_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_1_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 1) (realGauge.gaugeSizeL 4 3 1).1 (realGauge.gaugeSizeL 4 3 1).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_3_1_2 TL4_3_1 YLb4_3_1_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb4_3_1_3 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 1) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb4_3_1_3 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_1 (fuseRow ((4 : ZMod 8) + 3) (1 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb4_3_1_3 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb4_3_1_3 : List (List (List ℤ)) :=
  [[[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]]]

noncomputable def Xcb4_3_1_3 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_1_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_1_3 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_1_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_1_3 : ∀ I J g, Xb4_3_1_3 I J g = Xcb4_3_1_3 I J g := by
  decide +kernel

theorem hYtabb4_3_1_3 : ∀ I J g, Yb4_3_1_3 I J g = Ycb4_3_1_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb4_3_1_3 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_1
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_1 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xb4_3_1_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 hfuseZ_3_1 hfuseZ_4_4 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xcb4_3_1_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_1_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Yb4_3_1_3 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hfuseZ_4_3 hfuseZ_7_1 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Ycb4_3_1_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_1_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 1) (realGauge.gaugeSizeL 4 3 1).1 (realGauge.gaugeSizeL 4 3 1).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_3_1_3 TL4_3_1 YLb4_3_1_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Xb4_3_1_4 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 1) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Yb4_3_1_4 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_1 (fuseRow ((4 : ZMod 8) + 3) (1 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `4`, pre-tabulated. -/
def XLb4_3_1_4 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]]]

/-- Left route at the `b`-slot generator `4`, pre-tabulated. -/
def YLb4_3_1_4 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xcb4_3_1_4 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_1_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_1_4 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_1_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_1_4 : ∀ I J g, Xb4_3_1_4 I J g = Xcb4_3_1_4 I J g := by
  decide +kernel

theorem hYtabb4_3_1_4 : ∀ I J g, Yb4_3_1_4 I J g = Ycb4_3_1_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `4`** (Koszul sign `-1`). -/
theorem hintb4_3_1_4 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_1
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_1 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xb4_3_1_4 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 hfuseZ_3_1 hfuseZ_4_4 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xcb4_3_1_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_1_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Yb4_3_1_4 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hfuseZ_4_3 hfuseZ_7_1 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Ycb4_3_1_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_1_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 1) (realGauge.gaugeSizeL 4 3 1).1 (realGauge.gaugeSizeL 4 3 1).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_3_1_4 TL4_3_1 YLb4_3_1_4 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Xb4_3_1_5 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 1) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Yb4_3_1_5 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_1 (fuseRow ((4 : ZMod 8) + 3) (1 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `5`, pre-tabulated. -/
def XLb4_3_1_5 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]]]

/-- Left route at the `b`-slot generator `5`, pre-tabulated. -/
def YLb4_3_1_5 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

noncomputable def Xcb4_3_1_5 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_1_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_1_5 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_1_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_1_5 : ∀ I J g, Xb4_3_1_5 I J g = Xcb4_3_1_5 I J g := by
  decide +kernel

theorem hYtabb4_3_1_5 : ∀ I J g, Yb4_3_1_5 I J g = Ycb4_3_1_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintb4_3_1_5 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_1
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_1 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xb4_3_1_5 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 hfuseZ_3_1 hfuseZ_4_4 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xcb4_3_1_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_1_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Yb4_3_1_5 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hfuseZ_4_3 hfuseZ_7_1 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Ycb4_3_1_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_1_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 1) (realGauge.gaugeSizeL 4 3 1).1 (realGauge.gaugeSizeL 4 3 1).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_3_1_5 TL4_3_1 YLb4_3_1_5 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Xb4_3_1_6 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 1) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Yb4_3_1_6 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_1 (fuseRow ((4 : ZMod 8) + 3) (1 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `6`, pre-tabulated. -/
def XLb4_3_1_6 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

/-- Left route at the `b`-slot generator `6`, pre-tabulated. -/
def YLb4_3_1_6 : List (List (List ℤ)) :=
  [[[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

noncomputable def Xcb4_3_1_6 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_1_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_1_6 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_1_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_1_6 : ∀ I J g, Xb4_3_1_6 I J g = Xcb4_3_1_6 I J g := by
  decide +kernel

theorem hYtabb4_3_1_6 : ∀ I J g, Yb4_3_1_6 I J g = Ycb4_3_1_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintb4_3_1_6 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_1
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_1 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xb4_3_1_6 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 hfuseZ_3_1 hfuseZ_4_4 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xcb4_3_1_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_1_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Yb4_3_1_6 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hfuseZ_4_3 hfuseZ_7_1 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Ycb4_3_1_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_1_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 1) (realGauge.gaugeSizeL 4 3 1).1 (realGauge.gaugeSizeL 4 3 1).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_3_1_6 TL4_3_1 YLb4_3_1_6 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Xb4_3_1_7 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 1) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Yb4_3_1_7 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_1 (fuseRow ((4 : ZMod 8) + 3) (1 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `7`, pre-tabulated. -/
def XLb4_3_1_7 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `b`-slot generator `7`, pre-tabulated. -/
def YLb4_3_1_7 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]]]

noncomputable def Xcb4_3_1_7 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_1_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_1_7 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_1_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_1_7 : ∀ I J g, Xb4_3_1_7 I J g = Xcb4_3_1_7 I J g := by
  decide +kernel

theorem hYtabb4_3_1_7 : ∀ I J g, Yb4_3_1_7 I J g = Ycb4_3_1_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `7`** (Koszul sign `-1`). -/
theorem hintb4_3_1_7 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_1
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_1 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xb4_3_1_7 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 hfuseZ_3_1 hfuseZ_4_4 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xcb4_3_1_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_1_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Yb4_3_1_7 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hfuseZ_4_3 hfuseZ_7_1 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Ycb4_3_1_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_1_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 1) (realGauge.gaugeSizeL 4 3 1).1 (realGauge.gaugeSizeL 4 3 1).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_3_1_7 TL4_3_1 YLb4_3_1_7 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc4_3_1_0 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 1) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc4_3_1_0 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => if (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) = (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (3 : ZMod 8)).1 (realSize (4 : ZMod 8) (3 : ZMod 8)).2 (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I)
          * realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_7_1 (fuseRow ((4 : ZMod 8) + 3) (1 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc4_3_1_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc4_3_1_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xcc4_3_1_0 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet XLc4_3_1_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc4_3_1_0 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet YLc4_3_1_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc4_3_1_0 : ∀ I J g, Xc4_3_1_0 I J g = Xcc4_3_1_0 I J g := by
  decide +kernel

theorem hYtabc4_3_1_0 : ∀ I J g, Yc4_3_1_0 I J g = Ycc4_3_1_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc4_3_1_0 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T4_3_1
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_1 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xc4_3_1_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 hfuseZ_3_1 hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xcc4_3_1_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabc4_3_1_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Yc4_3_1_0 := Matrix.ext fun I J => routeL_cSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hfuseZ_7_1 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Ycc4_3_1_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabc4_3_1_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 1) (realGauge.gaugeSizeL 4 3 1).1 (realGauge.gaugeSizeL 4 3 1).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc4_3_1_0 TL4_3_1 YLc4_3_1_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc4_3_1_1 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) (ro (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 1) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 I) (ri (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc4_3_1_1 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun I J g => if (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) = (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (3 : ZMod 8)).1 (realSize (4 : ZMod 8) (3 : ZMod 8)).2 (lo (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I)
          * realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_7_1 (fuseRow ((4 : ZMod 8) + 3) (1 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc4_3_1_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc4_3_1_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]]]

noncomputable def Xcc4_3_1_1 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet XLc4_3_1_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc4_3_1_1 : (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 1).val) → ℤ :=
  fun r s g => coeffGet YLc4_3_1_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc4_3_1_1 : ∀ I J g, Xc4_3_1_1 I J g = Xcc4_3_1_1 I J g := by
  decide +kernel

theorem hYtabc4_3_1_1 : ∀ I J g, Yc4_3_1_1 I J g = Ycc4_3_1_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintc4_3_1_1 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T4_3_1
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_1 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xc4_3_1_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 hfuseZ_3_1 hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Xcc4_3_1_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabc4_3_1_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Yc4_3_1_1 := Matrix.ext fun I J => routeL_cSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hfuseZ_7_1 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 1)) Ycc4_3_1_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 1).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 1).2)) (realRepBasis ((4 : ZMod 8) + 3 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabc4_3_1_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 1) (realGauge.gaugeSizeL 4 3 1).1 (realGauge.gaugeSizeL 4 3 1).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc4_3_1_1 TL4_3_1 YLc4_3_1_1 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint4_3_1 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T4_3_1
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T4_3_1 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hinta4_3_1_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hinta4_3_1_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hinta4_3_1_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hinta4_3_1_3

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint4_3_1 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T4_3_1
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T4_3_1 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hintb4_3_1_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hintb4_3_1_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hintb4_3_1_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hintb4_3_1_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hintb4_3_1_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hintb4_3_1_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hintb4_3_1_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hintb4_3_1_7

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint4_3_1 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T4_3_1
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T4_3_1 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hintc4_3_1_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hintc4_3_1_1

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT4_3_1_mem_gInterSpace :
    gtOfT ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 T4_3_1 ∈ gInterSpace ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 hT4_3_1 hAint4_3_1 hBint4_3_1 hCint4_3_1

theorem gtOfT4_3_1_ne_zero : gtOfT ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 T4_3_1 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) hsz4_3_1 T4_3_1_ne_zero

theorem gInterSpace4_3_1_ne_bot : gInterSpace ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT4_3_1_mem_gInterSpace, gtOfT4_3_1_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_4_3_1 : gParity ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (1 : ZMod 8) gInterSpace4_3_1_ne_bot).symm

end Triple_4_3_1

/-! ### The triple `(4,3,2)`

`gaugeSizeL = gaugeSizeR = (4,4)`, `dim D_1 = 2`, certgen parity `1`; the transported connector literal. -/
section Triple_4_3_2
open Module
theorem hsz4_3_2 : realGauge.gaugeSizeR 4 3 2 = realGauge.gaugeSizeL 4 3 2 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`8 x 8 x 2`). -/
def TL4_3_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 1], [0, 0], [0, 0]]]

/-- The same literal read at the composite frame `Fin 4 ⊕ Fin 4`. -/
noncomputable def Tc4_3_2 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet TL4_3_2 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_1`. -/
noncomputable def T4_3_2 : ((realGauge.D ((4 : ZMod 8) + 3 + 2)).matrixSuper
    (realGauge.gaugeSizeL 4 3 2).1 (realGauge.gaugeSizeL 4 3 2).2).carrier :=
  matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Tc4_3_2

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT4_3_2 : T4_3_2 ∈ ((realGauge.D ((4 : ZMod 8) + 3 + 2)).matrixSuper
    (realGauge.gaugeSizeL 4 3 2).1 (realGauge.gaugeSizeL 4 3 2).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((4 : ZMod 8) + 3 + 2) Tc4_3_2 1 (by decide)

theorem T4_3_2_ne_zero : T4_3_2 ≠ 0 :=
  matOfCoeff_ne_zero ((4 : ZMod 8) + 3 + 2) Tc4_3_2 (Sum.inl ⟨0, by decide⟩) (Sum.inr ⟨1, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa4_3_2_0 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) = (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (2 : ZMod 8)).1 (realSize (3 : ZMod 8) (2 : ZMod 8)).2 (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I)
          * realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 2) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya4_3_2_0 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_2 (fuseRow ((4 : ZMod 8) + 3) (2 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa4_3_2_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa4_3_2_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xca4_3_2_0 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa4_3_2_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_3_2_0 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa4_3_2_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_3_2_0 : ∀ I J g, Xa4_3_2_0 I J g = Xca4_3_2_0 I J g := by
  decide +kernel

theorem hYtaba4_3_2_0 : ∀ I J g, Ya4_3_2_0 I J g = Yca4_3_2_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta4_3_2_0 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_3_2
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xa4_3_2_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xca4_3_2_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_3_2_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Ya4_3_2_0 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hfuseZ_4_3 hfuseZ_7_2 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Yca4_3_2_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_3_2_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 2) (realGauge.gaugeSizeL 4 3 2).1 (realGauge.gaugeSizeL 4 3 2).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa4_3_2_0 TL4_3_2 YLa4_3_2_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa4_3_2_1 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) = (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (2 : ZMod 8)).1 (realSize (3 : ZMod 8) (2 : ZMod 8)).2 (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I)
          * realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 2) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 2) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya4_3_2_1 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_2 (fuseRow ((4 : ZMod 8) + 3) (2 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa4_3_2_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa4_3_2_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]]]

noncomputable def Xca4_3_2_1 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa4_3_2_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_3_2_1 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa4_3_2_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_3_2_1 : ∀ I J g, Xa4_3_2_1 I J g = Xca4_3_2_1 I J g := by
  decide +kernel

theorem hYtaba4_3_2_1 : ∀ I J g, Ya4_3_2_1 I J g = Yca4_3_2_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta4_3_2_1 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_3_2
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xa4_3_2_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 hfuseZ_4_5 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xca4_3_2_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_3_2_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Ya4_3_2_1 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hfuseZ_4_3 hfuseZ_7_2 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Yca4_3_2_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_3_2_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 2) (realGauge.gaugeSizeL 4 3 2).1 (realGauge.gaugeSizeL 4 3 2).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa4_3_2_1 TL4_3_2 YLa4_3_2_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa4_3_2_2 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) = (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (2 : ZMod 8)).1 (realSize (3 : ZMod 8) (2 : ZMod 8)).2 (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I)
          * realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 2) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 2) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya4_3_2_2 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_2 (fuseRow ((4 : ZMod 8) + 3) (2 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa4_3_2_2 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa4_3_2_2 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]]]

noncomputable def Xca4_3_2_2 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa4_3_2_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_3_2_2 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa4_3_2_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_3_2_2 : ∀ I J g, Xa4_3_2_2 I J g = Xca4_3_2_2 I J g := by
  decide +kernel

theorem hYtaba4_3_2_2 : ∀ I J g, Ya4_3_2_2 I J g = Yca4_3_2_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta4_3_2_2 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_3_2
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xa4_3_2_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 hfuseZ_4_5 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xca4_3_2_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_3_2_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Ya4_3_2_2 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hfuseZ_4_3 hfuseZ_7_2 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Yca4_3_2_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_3_2_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 2) (realGauge.gaugeSizeL 4 3 2).1 (realGauge.gaugeSizeL 4 3 2).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa4_3_2_2 TL4_3_2 YLa4_3_2_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa4_3_2_3 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) = (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (2 : ZMod 8)).1 (realSize (3 : ZMod 8) (2 : ZMod 8)).2 (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I)
          * realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 2) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 2) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya4_3_2_3 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_2 (fuseRow ((4 : ZMod 8) + 3) (2 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa4_3_2_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa4_3_2_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca4_3_2_3 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa4_3_2_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_3_2_3 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa4_3_2_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_3_2_3 : ∀ I J g, Xa4_3_2_3 I J g = Xca4_3_2_3 I J g := by
  decide +kernel

theorem hYtaba4_3_2_3 : ∀ I J g, Ya4_3_2_3 I J g = Yca4_3_2_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta4_3_2_3 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_3_2
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xa4_3_2_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 hfuseZ_4_5 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xca4_3_2_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_3_2_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Ya4_3_2_3 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hfuseZ_4_3 hfuseZ_7_2 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Yca4_3_2_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_3_2_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 2) (realGauge.gaugeSizeL 4 3 2).1 (realGauge.gaugeSizeL 4 3 2).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa4_3_2_3 TL4_3_2 YLa4_3_2_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb4_3_2_0 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 2) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb4_3_2_0 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_2 (fuseRow ((4 : ZMod 8) + 3) (2 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb4_3_2_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb4_3_2_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcb4_3_2_0 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_2_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_2_0 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_2_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_2_0 : ∀ I J g, Xb4_3_2_0 I J g = Xcb4_3_2_0 I J g := by
  decide +kernel

theorem hYtabb4_3_2_0 : ∀ I J g, Yb4_3_2_0 I J g = Ycb4_3_2_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb4_3_2_0 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_2
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xb4_3_2_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 hfuseZ_3_2 hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xcb4_3_2_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_2_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Yb4_3_2_0 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hfuseZ_4_3 hfuseZ_7_2 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Ycb4_3_2_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_2_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 2) (realGauge.gaugeSizeL 4 3 2).1 (realGauge.gaugeSizeL 4 3 2).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_3_2_0 TL4_3_2 YLb4_3_2_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb4_3_2_1 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 2) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb4_3_2_1 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_2 (fuseRow ((4 : ZMod 8) + 3) (2 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb4_3_2_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb4_3_2_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb4_3_2_1 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_2_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_2_1 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_2_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_2_1 : ∀ I J g, Xb4_3_2_1 I J g = Xcb4_3_2_1 I J g := by
  decide +kernel

theorem hYtabb4_3_2_1 : ∀ I J g, Yb4_3_2_1 I J g = Ycb4_3_2_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintb4_3_2_1 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_2
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xb4_3_2_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 hfuseZ_3_2 hfuseZ_4_5 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xcb4_3_2_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_2_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Yb4_3_2_1 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hfuseZ_4_3 hfuseZ_7_2 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Ycb4_3_2_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_2_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 2) (realGauge.gaugeSizeL 4 3 2).1 (realGauge.gaugeSizeL 4 3 2).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_3_2_1 TL4_3_2 YLb4_3_2_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb4_3_2_2 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 2) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb4_3_2_2 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_2 (fuseRow ((4 : ZMod 8) + 3) (2 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb4_3_2_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb4_3_2_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb4_3_2_2 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_2_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_2_2 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_2_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_2_2 : ∀ I J g, Xb4_3_2_2 I J g = Xcb4_3_2_2 I J g := by
  decide +kernel

theorem hYtabb4_3_2_2 : ∀ I J g, Yb4_3_2_2 I J g = Ycb4_3_2_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintb4_3_2_2 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_2
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xb4_3_2_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 hfuseZ_3_2 hfuseZ_4_5 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xcb4_3_2_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_2_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Yb4_3_2_2 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hfuseZ_4_3 hfuseZ_7_2 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Ycb4_3_2_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_2_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 2) (realGauge.gaugeSizeL 4 3 2).1 (realGauge.gaugeSizeL 4 3 2).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_3_2_2 TL4_3_2 YLb4_3_2_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb4_3_2_3 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 2) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb4_3_2_3 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_2 (fuseRow ((4 : ZMod 8) + 3) (2 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb4_3_2_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb4_3_2_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]]]

noncomputable def Xcb4_3_2_3 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_2_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_2_3 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_2_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_2_3 : ∀ I J g, Xb4_3_2_3 I J g = Xcb4_3_2_3 I J g := by
  decide +kernel

theorem hYtabb4_3_2_3 : ∀ I J g, Yb4_3_2_3 I J g = Ycb4_3_2_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb4_3_2_3 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_2
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xb4_3_2_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 hfuseZ_3_2 hfuseZ_4_5 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xcb4_3_2_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_2_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Yb4_3_2_3 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hfuseZ_4_3 hfuseZ_7_2 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Ycb4_3_2_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_2_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 2) (realGauge.gaugeSizeL 4 3 2).1 (realGauge.gaugeSizeL 4 3 2).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_3_2_3 TL4_3_2 YLb4_3_2_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Xb4_3_2_4 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 2) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Yb4_3_2_4 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_2 (fuseRow ((4 : ZMod 8) + 3) (2 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `4`, pre-tabulated. -/
def XLb4_3_2_4 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]]]

/-- Left route at the `b`-slot generator `4`, pre-tabulated. -/
def YLb4_3_2_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb4_3_2_4 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_2_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_2_4 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_2_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_2_4 : ∀ I J g, Xb4_3_2_4 I J g = Xcb4_3_2_4 I J g := by
  decide +kernel

theorem hYtabb4_3_2_4 : ∀ I J g, Yb4_3_2_4 I J g = Ycb4_3_2_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `4`** (Koszul sign `-1`). -/
theorem hintb4_3_2_4 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_2
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xb4_3_2_4 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 hfuseZ_3_2 hfuseZ_4_5 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xcb4_3_2_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_2_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Yb4_3_2_4 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hfuseZ_4_3 hfuseZ_7_2 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Ycb4_3_2_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_2_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 2) (realGauge.gaugeSizeL 4 3 2).1 (realGauge.gaugeSizeL 4 3 2).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_3_2_4 TL4_3_2 YLb4_3_2_4 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Xb4_3_2_5 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 2) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Yb4_3_2_5 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_2 (fuseRow ((4 : ZMod 8) + 3) (2 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `5`, pre-tabulated. -/
def XLb4_3_2_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `5`, pre-tabulated. -/
def YLb4_3_2_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb4_3_2_5 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_2_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_2_5 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_2_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_2_5 : ∀ I J g, Xb4_3_2_5 I J g = Xcb4_3_2_5 I J g := by
  decide +kernel

theorem hYtabb4_3_2_5 : ∀ I J g, Yb4_3_2_5 I J g = Ycb4_3_2_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintb4_3_2_5 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_2
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xb4_3_2_5 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 hfuseZ_3_2 hfuseZ_4_5 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xcb4_3_2_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_2_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Yb4_3_2_5 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hfuseZ_4_3 hfuseZ_7_2 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Ycb4_3_2_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_2_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 2) (realGauge.gaugeSizeL 4 3 2).1 (realGauge.gaugeSizeL 4 3 2).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_3_2_5 TL4_3_2 YLb4_3_2_5 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Xb4_3_2_6 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 2) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Yb4_3_2_6 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_2 (fuseRow ((4 : ZMod 8) + 3) (2 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `6`, pre-tabulated. -/
def XLb4_3_2_6 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `6`, pre-tabulated. -/
def YLb4_3_2_6 : List (List (List ℤ)) :=
  [[[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]]]

noncomputable def Xcb4_3_2_6 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_2_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_2_6 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_2_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_2_6 : ∀ I J g, Xb4_3_2_6 I J g = Xcb4_3_2_6 I J g := by
  decide +kernel

theorem hYtabb4_3_2_6 : ∀ I J g, Yb4_3_2_6 I J g = Ycb4_3_2_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintb4_3_2_6 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_2
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xb4_3_2_6 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 hfuseZ_3_2 hfuseZ_4_5 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xcb4_3_2_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_2_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Yb4_3_2_6 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hfuseZ_4_3 hfuseZ_7_2 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Ycb4_3_2_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_2_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 2) (realGauge.gaugeSizeL 4 3 2).1 (realGauge.gaugeSizeL 4 3 2).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_3_2_6 TL4_3_2 YLb4_3_2_6 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Xb4_3_2_7 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 2) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Yb4_3_2_7 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_2 (fuseRow ((4 : ZMod 8) + 3) (2 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `7`, pre-tabulated. -/
def XLb4_3_2_7 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `7`, pre-tabulated. -/
def YLb4_3_2_7 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb4_3_2_7 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_2_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_2_7 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_2_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_2_7 : ∀ I J g, Xb4_3_2_7 I J g = Xcb4_3_2_7 I J g := by
  decide +kernel

theorem hYtabb4_3_2_7 : ∀ I J g, Yb4_3_2_7 I J g = Ycb4_3_2_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `7`** (Koszul sign `-1`). -/
theorem hintb4_3_2_7 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_2
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xb4_3_2_7 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 hfuseZ_3_2 hfuseZ_4_5 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xcb4_3_2_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_2_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Yb4_3_2_7 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hfuseZ_4_3 hfuseZ_7_2 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Ycb4_3_2_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_2_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 2) (realGauge.gaugeSizeL 4 3 2).1 (realGauge.gaugeSizeL 4 3 2).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_3_2_7 TL4_3_2 YLb4_3_2_7 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc4_3_2_0 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 2) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc4_3_2_0 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => if (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) = (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (3 : ZMod 8)).1 (realSize (4 : ZMod 8) (3 : ZMod 8)).2 (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_7_2 (fuseRow ((4 : ZMod 8) + 3) (2 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc4_3_2_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc4_3_2_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcc4_3_2_0 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc4_3_2_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc4_3_2_0 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc4_3_2_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc4_3_2_0 : ∀ I J g, Xc4_3_2_0 I J g = Xcc4_3_2_0 I J g := by
  decide +kernel

theorem hYtabc4_3_2_0 : ∀ I J g, Yc4_3_2_0 I J g = Ycc4_3_2_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc4_3_2_0 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T4_3_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xc4_3_2_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 hfuseZ_3_2 hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xcc4_3_2_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc4_3_2_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Yc4_3_2_0 := Matrix.ext fun I J => routeL_cSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hfuseZ_7_2 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Ycc4_3_2_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc4_3_2_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 2) (realGauge.gaugeSizeL 4 3 2).1 (realGauge.gaugeSizeL 4 3 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc4_3_2_0 TL4_3_2 YLc4_3_2_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc4_3_2_1 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 2) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc4_3_2_1 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => if (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) = (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (3 : ZMod 8)).1 (realSize (4 : ZMod 8) (3 : ZMod 8)).2 (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_7_2 (fuseRow ((4 : ZMod 8) + 3) (2 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc4_3_2_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc4_3_2_1 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]]]

noncomputable def Xcc4_3_2_1 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc4_3_2_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc4_3_2_1 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc4_3_2_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc4_3_2_1 : ∀ I J g, Xc4_3_2_1 I J g = Xcc4_3_2_1 I J g := by
  decide +kernel

theorem hYtabc4_3_2_1 : ∀ I J g, Yc4_3_2_1 I J g = Ycc4_3_2_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintc4_3_2_1 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T4_3_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xc4_3_2_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 hfuseZ_3_2 hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xcc4_3_2_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc4_3_2_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Yc4_3_2_1 := Matrix.ext fun I J => routeL_cSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hfuseZ_7_2 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Ycc4_3_2_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc4_3_2_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 2) (realGauge.gaugeSizeL 4 3 2).1 (realGauge.gaugeSizeL 4 3 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc4_3_2_1 TL4_3_2 YLc4_3_2_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc4_3_2_2 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 2) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc4_3_2_2 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => if (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) = (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (3 : ZMod 8)).1 (realSize (4 : ZMod 8) (3 : ZMod 8)).2 (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_7_2 (fuseRow ((4 : ZMod 8) + 3) (2 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc4_3_2_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc4_3_2_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc4_3_2_2 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc4_3_2_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc4_3_2_2 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc4_3_2_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc4_3_2_2 : ∀ I J g, Xc4_3_2_2 I J g = Xcc4_3_2_2 I J g := by
  decide +kernel

theorem hYtabc4_3_2_2 : ∀ I J g, Yc4_3_2_2 I J g = Ycc4_3_2_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintc4_3_2_2 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T4_3_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xc4_3_2_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 hfuseZ_3_2 hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xcc4_3_2_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc4_3_2_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Yc4_3_2_2 := Matrix.ext fun I J => routeL_cSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hfuseZ_7_2 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Ycc4_3_2_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc4_3_2_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 2) (realGauge.gaugeSizeL 4 3 2).1 (realGauge.gaugeSizeL 4 3 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc4_3_2_2 TL4_3_2 YLc4_3_2_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc4_3_2_3 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ro (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 2) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 I) (ri (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc4_3_2_3 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun I J g => if (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) = (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (3 : ZMod 8)).1 (realSize (4 : ZMod 8) (3 : ZMod 8)).2 (lo (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_7_2 (fuseRow ((4 : ZMod 8) + 3) (2 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc4_3_2_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc4_3_2_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc4_3_2_3 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc4_3_2_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc4_3_2_3 : (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc4_3_2_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc4_3_2_3 : ∀ I J g, Xc4_3_2_3 I J g = Xcc4_3_2_3 I J g := by
  decide +kernel

theorem hYtabc4_3_2_3 : ∀ I J g, Yc4_3_2_3 I J g = Ycc4_3_2_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc4_3_2_3 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T4_3_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_3_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xc4_3_2_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 hfuseZ_3_2 hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Xcc4_3_2_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc4_3_2_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Yc4_3_2_3 := Matrix.ext fun I J => routeL_cSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hfuseZ_7_2 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 2)) Ycc4_3_2_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 2).2)) (realRepBasis ((4 : ZMod 8) + 3 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc4_3_2_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 2) (realGauge.gaugeSizeL 4 3 2).1 (realGauge.gaugeSizeL 4 3 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc4_3_2_3 TL4_3_2 YLc4_3_2_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint4_3_2 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T4_3_2
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T4_3_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hinta4_3_2_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hinta4_3_2_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hinta4_3_2_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hinta4_3_2_3

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint4_3_2 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T4_3_2
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T4_3_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hintb4_3_2_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hintb4_3_2_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hintb4_3_2_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hintb4_3_2_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hintb4_3_2_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hintb4_3_2_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hintb4_3_2_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hintb4_3_2_7

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint4_3_2 (i : Fin (realRepDim (2 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) i)) * T4_3_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T4_3_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h0]; exact hintc4_3_2_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h1]; exact hintc4_3_2_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h2]; exact hintc4_3_2_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h3]; exact hintc4_3_2_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT4_3_2_mem_gInterSpace :
    gtOfT ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 T4_3_2 ∈ gInterSpace ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 hT4_3_2 hAint4_3_2 hBint4_3_2 hCint4_3_2

theorem gtOfT4_3_2_ne_zero : gtOfT ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 T4_3_2 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) hsz4_3_2 T4_3_2_ne_zero

theorem gInterSpace4_3_2_ne_bot : gInterSpace ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT4_3_2_mem_gInterSpace, gtOfT4_3_2_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_4_3_2 : gParity ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (2 : ZMod 8) gInterSpace4_3_2_ne_bot).symm

end Triple_4_3_2

/-! ### The triple `(4,3,4)`

`gaugeSizeL = gaugeSizeR = (2,2)`, `dim D_3 = 8`, certgen parity `0`; the transported connector literal. -/
section Triple_4_3_4
open Module
theorem hsz4_3_4 : realGauge.gaugeSizeR 4 3 4 = realGauge.gaugeSizeL 4 3 4 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`4 x 4 x 8`). -/
def TL4_3_4 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0]],
   [[0, 0, 0, 0, -1, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, -1, 0]],
   [[0, 0, -1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- The same literal read at the composite frame `Fin 2 ⊕ Fin 2`. -/
noncomputable def Tc4_3_4 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet TL4_3_4 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_3`. -/
noncomputable def T4_3_4 : ((realGauge.D ((4 : ZMod 8) + 3 + 4)).matrixSuper
    (realGauge.gaugeSizeL 4 3 4).1 (realGauge.gaugeSizeL 4 3 4).2).carrier :=
  matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Tc4_3_4

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT4_3_4 : T4_3_4 ∈ ((realGauge.D ((4 : ZMod 8) + 3 + 4)).matrixSuper
    (realGauge.gaugeSizeL 4 3 4).1 (realGauge.gaugeSizeL 4 3 4).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((4 : ZMod 8) + 3 + 4) Tc4_3_4 0 (by decide)

theorem T4_3_4_ne_zero : T4_3_4 ≠ 0 :=
  matOfCoeff_ne_zero ((4 : ZMod 8) + 3 + 4) Tc4_3_4 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa4_3_4_0 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) = (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (4 : ZMod 8)).1 (realSize (3 : ZMod 8) (4 : ZMod 8)).2 (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I)
          * realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 4) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya4_3_4_0 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_4 (fuseRow ((4 : ZMod 8) + 3) (4 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa4_3_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa4_3_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca4_3_4_0 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa4_3_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_3_4_0 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa4_3_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_3_4_0 : ∀ I J g, Xa4_3_4_0 I J g = Xca4_3_4_0 I J g := by
  decide +kernel

theorem hYtaba4_3_4_0 : ∀ I J g, Ya4_3_4_0 I J g = Yca4_3_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta4_3_4_0 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_3_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xa4_3_4_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xca4_3_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_3_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Ya4_3_4_0 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_4_3 hfuseZ_7_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Yca4_3_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_3_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 4 3 4).1 (realGauge.gaugeSizeL 4 3 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa4_3_4_0 TL4_3_4 YLa4_3_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa4_3_4_1 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) = (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (4 : ZMod 8)).1 (realSize (3 : ZMod 8) (4 : ZMod 8)).2 (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I)
          * realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 4) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 4) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya4_3_4_1 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_4 (fuseRow ((4 : ZMod 8) + 3) (4 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa4_3_4_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa4_3_4_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]],
   [[0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca4_3_4_1 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa4_3_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_3_4_1 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa4_3_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_3_4_1 : ∀ I J g, Xa4_3_4_1 I J g = Xca4_3_4_1 I J g := by
  decide +kernel

theorem hYtaba4_3_4_1 : ∀ I J g, Ya4_3_4_1 I J g = Yca4_3_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta4_3_4_1 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_3_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xa4_3_4_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 hfuseZ_4_7 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xca4_3_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_3_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Ya4_3_4_1 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_4_3 hfuseZ_7_4 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Yca4_3_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_3_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 4 3 4).1 (realGauge.gaugeSizeL 4 3 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa4_3_4_1 TL4_3_4 YLa4_3_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa4_3_4_2 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) = (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (4 : ZMod 8)).1 (realSize (3 : ZMod 8) (4 : ZMod 8)).2 (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I)
          * realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 4) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 4) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya4_3_4_2 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_4 (fuseRow ((4 : ZMod 8) + 3) (4 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa4_3_4_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa4_3_4_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca4_3_4_2 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa4_3_4_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_3_4_2 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa4_3_4_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_3_4_2 : ∀ I J g, Xa4_3_4_2 I J g = Xca4_3_4_2 I J g := by
  decide +kernel

theorem hYtaba4_3_4_2 : ∀ I J g, Ya4_3_4_2 I J g = Yca4_3_4_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta4_3_4_2 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_3_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xa4_3_4_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 hfuseZ_4_7 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xca4_3_4_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_3_4_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Ya4_3_4_2 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_4_3 hfuseZ_7_4 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Yca4_3_4_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_3_4_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 4 3 4).1 (realGauge.gaugeSizeL 4 3 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa4_3_4_2 TL4_3_4 YLa4_3_4_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa4_3_4_3 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) = (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (4 : ZMod 8)).1 (realSize (3 : ZMod 8) (4 : ZMod 8)).2 (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I)
          * realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 4) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 4) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya4_3_4_3 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_4 (fuseRow ((4 : ZMod 8) + 3) (4 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa4_3_4_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa4_3_4_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca4_3_4_3 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa4_3_4_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_3_4_3 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa4_3_4_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_3_4_3 : ∀ I J g, Xa4_3_4_3 I J g = Xca4_3_4_3 I J g := by
  decide +kernel

theorem hYtaba4_3_4_3 : ∀ I J g, Ya4_3_4_3 I J g = Yca4_3_4_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta4_3_4_3 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_3_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xa4_3_4_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 hfuseZ_4_7 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xca4_3_4_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_3_4_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Ya4_3_4_3 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_4_3 hfuseZ_7_4 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Yca4_3_4_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_3_4_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 4 3 4).1 (realGauge.gaugeSizeL 4 3 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa4_3_4_3 TL4_3_4 YLa4_3_4_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb4_3_4_0 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_4 (fuseRow (3 : ZMod 8) (4 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) ee) (fuseCol (3 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 4) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb4_3_4_0 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_4 (fuseRow ((4 : ZMod 8) + 3) (4 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb4_3_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb4_3_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb4_3_4_0 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_4_0 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_4_0 : ∀ I J g, Xb4_3_4_0 I J g = Xcb4_3_4_0 I J g := by
  decide +kernel

theorem hYtabb4_3_4_0 : ∀ I J g, Yb4_3_4_0 I J g = Ycb4_3_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb4_3_4_0 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xb4_3_4_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 hfuseZ_3_4 hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xcb4_3_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Yb4_3_4_0 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_4_3 hfuseZ_7_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Ycb4_3_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 4 3 4).1 (realGauge.gaugeSizeL 4 3 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_3_4_0 TL4_3_4 YLb4_3_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb4_3_4_1 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_4 (fuseRow (3 : ZMod 8) (4 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) ee) (fuseCol (3 : ZMod 8) (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 4) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb4_3_4_1 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_4 (fuseRow ((4 : ZMod 8) + 3) (4 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb4_3_4_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb4_3_4_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb4_3_4_1 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_4_1 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_4_1 : ∀ I J g, Xb4_3_4_1 I J g = Xcb4_3_4_1 I J g := by
  decide +kernel

theorem hYtabb4_3_4_1 : ∀ I J g, Yb4_3_4_1 I J g = Ycb4_3_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb4_3_4_1 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xb4_3_4_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 hfuseZ_3_4 hfuseZ_4_7 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xcb4_3_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Yb4_3_4_1 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_4_3 hfuseZ_7_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Ycb4_3_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 4 3 4).1 (realGauge.gaugeSizeL 4 3 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_3_4_1 TL4_3_4 YLb4_3_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb4_3_4_2 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_4 (fuseRow (3 : ZMod 8) (4 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) ee) (fuseCol (3 : ZMod 8) (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 4) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb4_3_4_2 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_4 (fuseRow ((4 : ZMod 8) + 3) (4 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb4_3_4_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb4_3_4_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb4_3_4_2 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_4_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_4_2 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_4_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_4_2 : ∀ I J g, Xb4_3_4_2 I J g = Xcb4_3_4_2 I J g := by
  decide +kernel

theorem hYtabb4_3_4_2 : ∀ I J g, Yb4_3_4_2 I J g = Ycb4_3_4_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb4_3_4_2 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xb4_3_4_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 hfuseZ_3_4 hfuseZ_4_7 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xcb4_3_4_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_4_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Yb4_3_4_2 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_4_3 hfuseZ_7_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Ycb4_3_4_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_4_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 4 3 4).1 (realGauge.gaugeSizeL 4 3 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_3_4_2 TL4_3_4 YLb4_3_4_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb4_3_4_3 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_4 (fuseRow (3 : ZMod 8) (4 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) ee) (fuseCol (3 : ZMod 8) (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 4) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb4_3_4_3 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_4 (fuseRow ((4 : ZMod 8) + 3) (4 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb4_3_4_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]],
   [[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb4_3_4_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]],
   [[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb4_3_4_3 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_4_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_4_3 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_4_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_4_3 : ∀ I J g, Xb4_3_4_3 I J g = Xcb4_3_4_3 I J g := by
  decide +kernel

theorem hYtabb4_3_4_3 : ∀ I J g, Yb4_3_4_3 I J g = Ycb4_3_4_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb4_3_4_3 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xb4_3_4_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 hfuseZ_3_4 hfuseZ_4_7 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xcb4_3_4_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_4_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Yb4_3_4_3 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_4_3 hfuseZ_7_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Ycb4_3_4_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_4_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 4 3 4).1 (realGauge.gaugeSizeL 4 3 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_3_4_3 TL4_3_4 YLb4_3_4_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Xb4_3_4_4 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_4 (fuseRow (3 : ZMod 8) (4 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) ee) (fuseCol (3 : ZMod 8) (4 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 4) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Yb4_3_4_4 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_4 (fuseRow ((4 : ZMod 8) + 3) (4 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `4`, pre-tabulated. -/
def XLb4_3_4_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `4`, pre-tabulated. -/
def YLb4_3_4_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb4_3_4_4 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_4_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_4_4 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_4_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_4_4 : ∀ I J g, Xb4_3_4_4 I J g = Xcb4_3_4_4 I J g := by
  decide +kernel

theorem hYtabb4_3_4_4 : ∀ I J g, Yb4_3_4_4 I J g = Ycb4_3_4_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `4`** (Koszul sign `+1`). -/
theorem hintb4_3_4_4 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xb4_3_4_4 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 hfuseZ_3_4 hfuseZ_4_7 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xcb4_3_4_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_4_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Yb4_3_4_4 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_4_3 hfuseZ_7_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Ycb4_3_4_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_4_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 4 3 4).1 (realGauge.gaugeSizeL 4 3 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_3_4_4 TL4_3_4 YLb4_3_4_4 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Xb4_3_4_5 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_4 (fuseRow (3 : ZMod 8) (4 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) ee) (fuseCol (3 : ZMod 8) (4 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 4) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Yb4_3_4_5 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_4 (fuseRow ((4 : ZMod 8) + 3) (4 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `5`, pre-tabulated. -/
def XLb4_3_4_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `5`, pre-tabulated. -/
def YLb4_3_4_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb4_3_4_5 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_4_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_4_5 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_4_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_4_5 : ∀ I J g, Xb4_3_4_5 I J g = Xcb4_3_4_5 I J g := by
  decide +kernel

theorem hYtabb4_3_4_5 : ∀ I J g, Yb4_3_4_5 I J g = Ycb4_3_4_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintb4_3_4_5 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xb4_3_4_5 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 hfuseZ_3_4 hfuseZ_4_7 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xcb4_3_4_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_4_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Yb4_3_4_5 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_4_3 hfuseZ_7_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Ycb4_3_4_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_4_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 4 3 4).1 (realGauge.gaugeSizeL 4 3 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_3_4_5 TL4_3_4 YLb4_3_4_5 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Xb4_3_4_6 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_4 (fuseRow (3 : ZMod 8) (4 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) ee) (fuseCol (3 : ZMod 8) (4 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 4) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Yb4_3_4_6 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_4 (fuseRow ((4 : ZMod 8) + 3) (4 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `6`, pre-tabulated. -/
def XLb4_3_4_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `6`, pre-tabulated. -/
def YLb4_3_4_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb4_3_4_6 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_4_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_4_6 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_4_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_4_6 : ∀ I J g, Xb4_3_4_6 I J g = Xcb4_3_4_6 I J g := by
  decide +kernel

theorem hYtabb4_3_4_6 : ∀ I J g, Yb4_3_4_6 I J g = Ycb4_3_4_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintb4_3_4_6 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xb4_3_4_6 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 hfuseZ_3_4 hfuseZ_4_7 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xcb4_3_4_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_4_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Yb4_3_4_6 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_4_3 hfuseZ_7_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Ycb4_3_4_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_4_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 4 3 4).1 (realGauge.gaugeSizeL 4 3 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_3_4_6 TL4_3_4 YLb4_3_4_6 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Xb4_3_4_7 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_4 (fuseRow (3 : ZMod 8) (4 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) ee) (fuseCol (3 : ZMod 8) (4 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 4) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Yb4_3_4_7 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_7_4 (fuseRow ((4 : ZMod 8) + 3) (4 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `7`, pre-tabulated. -/
def XLb4_3_4_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1]]]

/-- Left route at the `b`-slot generator `7`, pre-tabulated. -/
def YLb4_3_4_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1]]]

noncomputable def Xcb4_3_4_7 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb4_3_4_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_3_4_7 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb4_3_4_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_3_4_7 : ∀ I J g, Xb4_3_4_7 I J g = Xcb4_3_4_7 I J g := by
  decide +kernel

theorem hYtabb4_3_4_7 : ∀ I J g, Yb4_3_4_7 I J g = Ycb4_3_4_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `7`** (Koszul sign `+1`). -/
theorem hintb4_3_4_7 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T4_3_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xb4_3_4_7 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 hfuseZ_3_4 hfuseZ_4_7 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xcb4_3_4_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_3_4_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Yb4_3_4_7 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_4_3 hfuseZ_7_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Ycb4_3_4_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_3_4_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 4 3 4).1 (realGauge.gaugeSizeL 4 3 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_3_4_7 TL4_3_4 YLb4_3_4_7 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc4_3_4_0 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_4 (fuseRow (3 : ZMod 8) (4 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) ee) (fuseCol (3 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 4) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc4_3_4_0 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => if (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) = (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (3 : ZMod 8)).1 (realSize (4 : ZMod 8) (3 : ZMod 8)).2 (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_7_4 (fuseRow ((4 : ZMod 8) + 3) (4 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc4_3_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc4_3_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcc4_3_4_0 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc4_3_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc4_3_4_0 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc4_3_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc4_3_4_0 : ∀ I J g, Xc4_3_4_0 I J g = Xcc4_3_4_0 I J g := by
  decide +kernel

theorem hYtabc4_3_4_0 : ∀ I J g, Yc4_3_4_0 I J g = Ycc4_3_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc4_3_4_0 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_3_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xc4_3_4_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 hfuseZ_3_4 hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xcc4_3_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc4_3_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Yc4_3_4_0 := Matrix.ext fun I J => routeL_cSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_7_4 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Ycc4_3_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc4_3_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 4 3 4).1 (realGauge.gaugeSizeL 4 3 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc4_3_4_0 TL4_3_4 YLc4_3_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc4_3_4_1 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_4 (fuseRow (3 : ZMod 8) (4 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) ee) (fuseCol (3 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 4) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc4_3_4_1 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => if (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) = (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (3 : ZMod 8)).1 (realSize (4 : ZMod 8) (3 : ZMod 8)).2 (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_7_4 (fuseRow ((4 : ZMod 8) + 3) (4 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc4_3_4_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]],
   [[0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc4_3_4_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]]]

noncomputable def Xcc4_3_4_1 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc4_3_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc4_3_4_1 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc4_3_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc4_3_4_1 : ∀ I J g, Xc4_3_4_1 I J g = Xcc4_3_4_1 I J g := by
  decide +kernel

theorem hYtabc4_3_4_1 : ∀ I J g, Yc4_3_4_1 I J g = Ycc4_3_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc4_3_4_1 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_3_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xc4_3_4_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 hfuseZ_3_4 hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xcc4_3_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc4_3_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Yc4_3_4_1 := Matrix.ext fun I J => routeL_cSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_7_4 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Ycc4_3_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc4_3_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 4 3 4).1 (realGauge.gaugeSizeL 4 3 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc4_3_4_1 TL4_3_4 YLc4_3_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc4_3_4_2 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_4 (fuseRow (3 : ZMod 8) (4 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) ee) (fuseCol (3 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 4) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc4_3_4_2 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => if (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) = (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (3 : ZMod 8)).1 (realSize (4 : ZMod 8) (3 : ZMod 8)).2 (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_7_4 (fuseRow ((4 : ZMod 8) + 3) (4 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc4_3_4_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc4_3_4_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]]]

noncomputable def Xcc4_3_4_2 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc4_3_4_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc4_3_4_2 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc4_3_4_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc4_3_4_2 : ∀ I J g, Xc4_3_4_2 I J g = Xcc4_3_4_2 I J g := by
  decide +kernel

theorem hYtabc4_3_4_2 : ∀ I J g, Yc4_3_4_2 I J g = Ycc4_3_4_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc4_3_4_2 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_3_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xc4_3_4_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 hfuseZ_3_4 hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xcc4_3_4_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc4_3_4_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Yc4_3_4_2 := Matrix.ext fun I J => routeL_cSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_7_4 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Ycc4_3_4_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc4_3_4_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 4 3 4).1 (realGauge.gaugeSizeL 4 3 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc4_3_4_2 TL4_3_4 YLc4_3_4_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc4_3_4_3 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_4 (fuseRow (3 : ZMod 8) (4 : ZMod 8) (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ro (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) ee) (fuseCol (3 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((3 : ZMod 8) + 4) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 I) (ri (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 J) g) (fuseCol (4 : ZMod 8) ((3 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc4_3_4_3 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => if (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) = (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (3 : ZMod 8)).1 (realSize (4 : ZMod 8) (3 : ZMod 8)).2 (lo (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_7_4 (fuseRow ((4 : ZMod 8) + 3) (4 : ZMod 8) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 3) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc4_3_4_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc4_3_4_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0]]]

noncomputable def Xcc4_3_4_3 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc4_3_4_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc4_3_4_3 : (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2) → Fin (realRepDim ((4 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc4_3_4_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc4_3_4_3 : ∀ I J g, Xc4_3_4_3 I J g = Xcc4_3_4_3 I J g := by
  decide +kernel

theorem hYtabc4_3_4_3 : ∀ I J g, Yc4_3_4_3 I J g = Ycc4_3_4_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc4_3_4_3 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_3_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_3_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xc4_3_4_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 hfuseZ_3_4 hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Xcc4_3_4_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc4_3_4_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Yc4_3_4_3 := Matrix.ext fun I J => routeL_cSlot_coeff (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_7_4 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 3 + 4)) Ycc4_3_4_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 3 4).2)) (realRepBasis ((4 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc4_3_4_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 4 3 4).1 (realGauge.gaugeSizeL 4 3 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc4_3_4_3 TL4_3_4 YLc4_3_4_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint4_3_4 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T4_3_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T4_3_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hinta4_3_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hinta4_3_4_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hinta4_3_4_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hinta4_3_4_3

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint4_3_4 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T4_3_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T4_3_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hintb4_3_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hintb4_3_4_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hintb4_3_4_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hintb4_3_4_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hintb4_3_4_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hintb4_3_4_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hintb4_3_4_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hintb4_3_4_7

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint4_3_4 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T4_3_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T4_3_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hintc4_3_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hintc4_3_4_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hintc4_3_4_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hintc4_3_4_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT4_3_4_mem_gInterSpace :
    gtOfT ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 T4_3_4 ∈ gInterSpace ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 hT4_3_4 hAint4_3_4 hBint4_3_4 hCint4_3_4

theorem gtOfT4_3_4_ne_zero : gtOfT ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 T4_3_4 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz4_3_4 T4_3_4_ne_zero

theorem gInterSpace4_3_4_ne_bot : gInterSpace ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT4_3_4_mem_gInterSpace, gtOfT4_3_4_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_4_3_4 : gParity ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (4 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) gInterSpace4_3_4_ne_bot).symm

end Triple_4_3_4

end G4_7
end TripleCerts
end GaugeChi
end Superfusion

/-! ### Kernel self-check -/

#print axioms Superfusion.GaugeChi.TripleCerts.G4_7.gParity_4_2_7
#print axioms Superfusion.GaugeChi.TripleCerts.G4_7.gParity_4_3_0
#print axioms Superfusion.GaugeChi.TripleCerts.G4_7.gParity_4_3_1
#print axioms Superfusion.GaugeChi.TripleCerts.G4_7.gParity_4_3_2
#print axioms Superfusion.GaugeChi.TripleCerts.G4_7.gParity_4_3_4
