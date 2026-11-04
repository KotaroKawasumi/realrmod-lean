/-
Superfusion / GaugeChi / TripleCerts / G5_18

**GENERATED FILE — do not edit.**  Regenerate with

    python3 scripts/certgen/gen_triple_certs.py \
        --triples 5,4,1 5,4,2 5,4,6 5,4,7 5,5,0 \
        --module G5_18 \
        --out Superfusion/GaugeChi/TripleCerts/G5_18.lean

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

Triples (5): (5,4,1), (5,4,2), (5,4,6), (5,4,7), (5,5,0).
Unit-slot triples (`a = 0` or `b = 0` or `c = 0`) in this batch: (5,5,0).
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
namespace G5_18

open Module

/-! ### The fusion shadows this batch uses (15 of the 64)

They are declared at the enclosing `TripleCerts` namespace by
`TripleCerts/FuseShadows.lean`, so the short names below resolve
unqualified and no `open` is needed:

  `fuseZ_1_1`, `fuseZ_1_2`, `fuseZ_1_6`, `fuseZ_1_7`, `fuseZ_2_0`, `fuseZ_4_1`, `fuseZ_4_2`, `fuseZ_4_6`, `fuseZ_4_7`, `fuseZ_5_0`, `fuseZ_5_2`, `fuseZ_5_3`, `fuseZ_5_4`, `fuseZ_5_5`, `fuseZ_5_6`. -/

/-! ### The triple `(5,4,1)`

`gaugeSizeL = gaugeSizeR = (2,2)`, `dim D_2 = 4`, certgen parity `1`; the transported connector literal. -/
section Triple_5_4_1
open Module
theorem hsz5_4_1 : realGauge.gaugeSizeR 5 4 1 = realGauge.gaugeSizeL 5 4 1 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`4 x 4 x 4`). -/
def TL5_4_1 : List (List (List ℤ)) :=
  [[[0, -1, -1, 0], [0, -1, 1, 0], [-1, 0, 0, 1], [-1, 0, 0, -1]],
   [[0, 1, -1, 0], [0, 1, 1, 0], [1, 0, 0, 1], [1, 0, 0, -1]],
   [[-1, 0, 0, -1], [1, 0, 0, -1], [0, 1, -1, 0], [0, -1, -1, 0]],
   [[1, 0, 0, -1], [-1, 0, 0, -1], [0, -1, -1, 0], [0, 1, -1, 0]]]

/-- The same literal read at the composite frame `Fin 2 ⊕ Fin 2`. -/
noncomputable def Tc5_4_1 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet TL5_4_1 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_2`. -/
noncomputable def T5_4_1 : ((realGauge.D ((5 : ZMod 8) + 4 + 1)).matrixSuper
    (realGauge.gaugeSizeL 5 4 1).1 (realGauge.gaugeSizeL 5 4 1).2).carrier :=
  matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Tc5_4_1

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT5_4_1 : T5_4_1 ∈ ((realGauge.D ((5 : ZMod 8) + 4 + 1)).matrixSuper
    (realGauge.gaugeSizeL 5 4 1).1 (realGauge.gaugeSizeL 5 4 1).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((5 : ZMod 8) + 4 + 1) Tc5_4_1 1 (by decide)

theorem T5_4_1_ne_zero : T5_4_1 ≠ 0 :=
  matOfCoeff_ne_zero ((5 : ZMod 8) + 4 + 1) Tc5_4_1 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨1, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa5_4_1_0 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (1 : ZMod 8)).1 (realSize (4 : ZMod 8) (1 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I)
          * realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 1) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya5_4_1_0 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow ((5 : ZMod 8) + 4) (1 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa5_4_1_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa5_4_1_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xca5_4_1_0 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_1_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_1_0 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_1_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_1_0 : ∀ I J g, Xa5_4_1_0 I J g = Xca5_4_1_0 I J g := by
  decide +kernel

theorem hYtaba5_4_1_0 : ∀ I J g, Ya5_4_1_0 I J g = Yca5_4_1_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta5_4_1_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_1
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_4_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xa5_4_1_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 hfuseZ_5_5 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xca5_4_1_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_1_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Ya5_4_1_0 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_5_4 hfuseZ_1_1 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Yca5_4_1_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_1_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 5 4 1).1 (realGauge.gaugeSizeL 5 4 1).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_4_1_0 TL5_4_1 YLa5_4_1_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa5_4_1_1 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (1 : ZMod 8)).1 (realSize (4 : ZMod 8) (1 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I)
          * realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 1) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 1) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya5_4_1_1 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow ((5 : ZMod 8) + 4) (1 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa5_4_1_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa5_4_1_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca5_4_1_1 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_1_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_1_1 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_1_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_1_1 : ∀ I J g, Xa5_4_1_1 I J g = Xca5_4_1_1 I J g := by
  decide +kernel

theorem hYtaba5_4_1_1 : ∀ I J g, Ya5_4_1_1 I J g = Yca5_4_1_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `-1`). -/
theorem hinta5_4_1_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_1
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_4_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xa5_4_1_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 hfuseZ_5_5 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xca5_4_1_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_1_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Ya5_4_1_1 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_5_4 hfuseZ_1_1 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Yca5_4_1_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_1_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 5 4 1).1 (realGauge.gaugeSizeL 5 4 1).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_4_1_1 TL5_4_1 YLa5_4_1_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa5_4_1_2 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (1 : ZMod 8)).1 (realSize (4 : ZMod 8) (1 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I)
          * realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 1) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 1) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya5_4_1_2 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow ((5 : ZMod 8) + 4) (1 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa5_4_1_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa5_4_1_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca5_4_1_2 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_1_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_1_2 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_1_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_1_2 : ∀ I J g, Xa5_4_1_2 I J g = Xca5_4_1_2 I J g := by
  decide +kernel

theorem hYtaba5_4_1_2 : ∀ I J g, Ya5_4_1_2 I J g = Yca5_4_1_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `-1`). -/
theorem hinta5_4_1_2 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_1
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_4_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xa5_4_1_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 hfuseZ_5_5 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xca5_4_1_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_1_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Ya5_4_1_2 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_5_4 hfuseZ_1_1 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Yca5_4_1_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_1_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 5 4 1).1 (realGauge.gaugeSizeL 5 4 1).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_4_1_2 TL5_4_1 YLa5_4_1_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa5_4_1_3 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (1 : ZMod 8)).1 (realSize (4 : ZMod 8) (1 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I)
          * realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 1) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 1) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya5_4_1_3 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow ((5 : ZMod 8) + 4) (1 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa5_4_1_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa5_4_1_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca5_4_1_3 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_1_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_1_3 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_1_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_1_3 : ∀ I J g, Xa5_4_1_3 I J g = Xca5_4_1_3 I J g := by
  decide +kernel

theorem hYtaba5_4_1_3 : ∀ I J g, Ya5_4_1_3 I J g = Yca5_4_1_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta5_4_1_3 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_1
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_4_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xa5_4_1_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 hfuseZ_5_5 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xca5_4_1_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_1_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Ya5_4_1_3 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_5_4 hfuseZ_1_1 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Yca5_4_1_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_1_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 5 4 1).1 (realGauge.gaugeSizeL 5 4 1).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_4_1_3 TL5_4_1 YLa5_4_1_3 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Xa5_4_1_4 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (1 : ZMod 8)).1 (realSize (4 : ZMod 8) (1 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I)
          * realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 1) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 1) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Ya5_4_1_4 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow ((5 : ZMod 8) + 4) (1 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `4`, pre-tabulated. -/
def XLa5_4_1_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `4`, pre-tabulated. -/
def YLa5_4_1_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca5_4_1_4 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_1_4 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_1_4 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_1_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_1_4 : ∀ I J g, Xa5_4_1_4 I J g = Xca5_4_1_4 I J g := by
  decide +kernel

theorem hYtaba5_4_1_4 : ∀ I J g, Ya5_4_1_4 I J g = Yca5_4_1_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `4`** (Koszul sign `-1`). -/
theorem hinta5_4_1_4 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_1
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_4_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xa5_4_1_4 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 hfuseZ_5_5 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xca5_4_1_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_1_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Ya5_4_1_4 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_5_4 hfuseZ_1_1 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Yca5_4_1_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_1_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 5 4 1).1 (realGauge.gaugeSizeL 5 4 1).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_4_1_4 TL5_4_1 YLa5_4_1_4 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Xa5_4_1_5 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (1 : ZMod 8)).1 (realSize (4 : ZMod 8) (1 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I)
          * realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 1) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 1) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Ya5_4_1_5 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow ((5 : ZMod 8) + 4) (1 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `5`, pre-tabulated. -/
def XLa5_4_1_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `5`, pre-tabulated. -/
def YLa5_4_1_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca5_4_1_5 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_1_5 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_1_5 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_1_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_1_5 : ∀ I J g, Xa5_4_1_5 I J g = Xca5_4_1_5 I J g := by
  decide +kernel

theorem hYtaba5_4_1_5 : ∀ I J g, Ya5_4_1_5 I J g = Yca5_4_1_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `5`** (Koszul sign `+1`). -/
theorem hinta5_4_1_5 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_1
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_4_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xa5_4_1_5 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 hfuseZ_5_5 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xca5_4_1_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_1_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Ya5_4_1_5 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_5_4 hfuseZ_1_1 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Yca5_4_1_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_1_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 5 4 1).1 (realGauge.gaugeSizeL 5 4 1).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_4_1_5 TL5_4_1 YLa5_4_1_5 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Xa5_4_1_6 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (1 : ZMod 8)).1 (realSize (4 : ZMod 8) (1 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I)
          * realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 1) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 1) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Ya5_4_1_6 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow ((5 : ZMod 8) + 4) (1 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `6`, pre-tabulated. -/
def XLa5_4_1_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `6`, pre-tabulated. -/
def YLa5_4_1_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca5_4_1_6 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_1_6 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_1_6 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_1_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_1_6 : ∀ I J g, Xa5_4_1_6 I J g = Xca5_4_1_6 I J g := by
  decide +kernel

theorem hYtaba5_4_1_6 : ∀ I J g, Ya5_4_1_6 I J g = Yca5_4_1_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `6`** (Koszul sign `+1`). -/
theorem hinta5_4_1_6 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_1
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_4_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xa5_4_1_6 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 hfuseZ_5_5 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xca5_4_1_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_1_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Ya5_4_1_6 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_5_4 hfuseZ_1_1 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Yca5_4_1_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_1_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 5 4 1).1 (realGauge.gaugeSizeL 5 4 1).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_4_1_6 TL5_4_1 YLa5_4_1_6 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Xa5_4_1_7 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (1 : ZMod 8)).1 (realSize (4 : ZMod 8) (1 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I)
          * realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 1) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 1) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Ya5_4_1_7 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow ((5 : ZMod 8) + 4) (1 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `7`, pre-tabulated. -/
def XLa5_4_1_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `7`, pre-tabulated. -/
def YLa5_4_1_7 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]]]

noncomputable def Xca5_4_1_7 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_1_7 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_1_7 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_1_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_1_7 : ∀ I J g, Xa5_4_1_7 I J g = Xca5_4_1_7 I J g := by
  decide +kernel

theorem hYtaba5_4_1_7 : ∀ I J g, Ya5_4_1_7 I J g = Yca5_4_1_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `7`** (Koszul sign `-1`). -/
theorem hinta5_4_1_7 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_1
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_4_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xa5_4_1_7 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 hfuseZ_5_5 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xca5_4_1_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_1_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Ya5_4_1_7 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_5_4 hfuseZ_1_1 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Yca5_4_1_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_1_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 5 4 1).1 (realGauge.gaugeSizeL 5 4 1).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_4_1_7 TL5_4_1 YLa5_4_1_7 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb5_4_1_0 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_1 (fuseRow (4 : ZMod 8) (1 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) ee) (fuseCol (4 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 1) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb5_4_1_0 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow ((5 : ZMod 8) + 4) (1 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb5_4_1_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb5_4_1_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcb5_4_1_0 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLb5_4_1_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_4_1_0 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLb5_4_1_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_4_1_0 : ∀ I J g, Xb5_4_1_0 I J g = Xcb5_4_1_0 I J g := by
  decide +kernel

theorem hYtabb5_4_1_0 : ∀ I J g, Yb5_4_1_0 I J g = Ycb5_4_1_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb5_4_1_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T5_4_1
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_4_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xb5_4_1_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 hfuseZ_4_1 hfuseZ_5_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xcb5_4_1_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_4_1_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Yb5_4_1_0 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_5_4 hfuseZ_1_1 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Ycb5_4_1_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_4_1_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 5 4 1).1 (realGauge.gaugeSizeL 5 4 1).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb5_4_1_0 TL5_4_1 YLb5_4_1_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb5_4_1_1 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_1 (fuseRow (4 : ZMod 8) (1 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) ee) (fuseCol (4 : ZMod 8) (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 1) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb5_4_1_1 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow ((5 : ZMod 8) + 4) (1 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb5_4_1_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb5_4_1_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb5_4_1_1 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLb5_4_1_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_4_1_1 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLb5_4_1_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_4_1_1 : ∀ I J g, Xb5_4_1_1 I J g = Xcb5_4_1_1 I J g := by
  decide +kernel

theorem hYtabb5_4_1_1 : ∀ I J g, Yb5_4_1_1 I J g = Ycb5_4_1_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb5_4_1_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T5_4_1
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_4_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xb5_4_1_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 hfuseZ_4_1 hfuseZ_5_5 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xcb5_4_1_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_4_1_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Yb5_4_1_1 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_5_4 hfuseZ_1_1 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Ycb5_4_1_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_4_1_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 5 4 1).1 (realGauge.gaugeSizeL 5 4 1).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb5_4_1_1 TL5_4_1 YLb5_4_1_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb5_4_1_2 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_1 (fuseRow (4 : ZMod 8) (1 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) ee) (fuseCol (4 : ZMod 8) (1 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 1) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb5_4_1_2 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow ((5 : ZMod 8) + 4) (1 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb5_4_1_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb5_4_1_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb5_4_1_2 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLb5_4_1_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_4_1_2 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLb5_4_1_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_4_1_2 : ∀ I J g, Xb5_4_1_2 I J g = Xcb5_4_1_2 I J g := by
  decide +kernel

theorem hYtabb5_4_1_2 : ∀ I J g, Yb5_4_1_2 I J g = Ycb5_4_1_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb5_4_1_2 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T5_4_1
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_4_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xb5_4_1_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 hfuseZ_4_1 hfuseZ_5_5 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xcb5_4_1_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_4_1_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Yb5_4_1_2 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_5_4 hfuseZ_1_1 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Ycb5_4_1_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_4_1_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 5 4 1).1 (realGauge.gaugeSizeL 5 4 1).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb5_4_1_2 TL5_4_1 YLb5_4_1_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb5_4_1_3 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_1 (fuseRow (4 : ZMod 8) (1 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) ee) (fuseCol (4 : ZMod 8) (1 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 1) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb5_4_1_3 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_1 (fuseRow ((5 : ZMod 8) + 4) (1 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb5_4_1_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb5_4_1_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb5_4_1_3 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLb5_4_1_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_4_1_3 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLb5_4_1_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_4_1_3 : ∀ I J g, Xb5_4_1_3 I J g = Xcb5_4_1_3 I J g := by
  decide +kernel

theorem hYtabb5_4_1_3 : ∀ I J g, Yb5_4_1_3 I J g = Ycb5_4_1_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb5_4_1_3 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T5_4_1
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_4_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xb5_4_1_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 hfuseZ_4_1 hfuseZ_5_5 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xcb5_4_1_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_4_1_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Yb5_4_1_3 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_5_4 hfuseZ_1_1 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Ycb5_4_1_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_4_1_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 5 4 1).1 (realGauge.gaugeSizeL 5 4 1).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb5_4_1_3 TL5_4_1 YLb5_4_1_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc5_4_1_0 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_1 (fuseRow (4 : ZMod 8) (1 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) ee) (fuseCol (4 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 1) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc5_4_1_0 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) = (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (4 : ZMod 8)).1 (realSize (5 : ZMod 8) (4 : ZMod 8)).2 (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I)
          * realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_1 (fuseRow ((5 : ZMod 8) + 4) (1 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc5_4_1_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc5_4_1_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcc5_4_1_0 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLc5_4_1_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_4_1_0 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLc5_4_1_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_4_1_0 : ∀ I J g, Xc5_4_1_0 I J g = Xcc5_4_1_0 I J g := by
  decide +kernel

theorem hYtabc5_4_1_0 : ∀ I J g, Yc5_4_1_0 I J g = Ycc5_4_1_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc5_4_1_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T5_4_1
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_4_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xc5_4_1_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 hfuseZ_4_1 hfuseZ_5_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xcc5_4_1_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_4_1_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Yc5_4_1_0 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_1_1 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Ycc5_4_1_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_4_1_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 5 4 1).1 (realGauge.gaugeSizeL 5 4 1).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_4_1_0 TL5_4_1 YLc5_4_1_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc5_4_1_1 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_1 (fuseRow (4 : ZMod 8) (1 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) (ro (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) ee) (fuseCol (4 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 1) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 I) (ri (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc5_4_1_1 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) = (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (4 : ZMod 8)).1 (realSize (5 : ZMod 8) (4 : ZMod 8)).2 (lo (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I)
          * realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_1 (fuseRow ((5 : ZMod 8) + 4) (1 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc5_4_1_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc5_4_1_1 : List (List (List ℤ)) :=
  [[[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0]]]

noncomputable def Xcc5_4_1_1 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLc5_4_1_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_4_1_1 : (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLc5_4_1_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_4_1_1 : ∀ I J g, Xc5_4_1_1 I J g = Xcc5_4_1_1 I J g := by
  decide +kernel

theorem hYtabc5_4_1_1 : ∀ I J g, Yc5_4_1_1 I J g = Ycc5_4_1_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintc5_4_1_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T5_4_1
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_4_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xc5_4_1_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 hfuseZ_4_1 hfuseZ_5_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Xcc5_4_1_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_4_1_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Yc5_4_1_1 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_1_1 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 1)) Ycc5_4_1_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 1).2)) (realRepBasis ((5 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_4_1_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 5 4 1).1 (realGauge.gaugeSizeL 5 4 1).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_4_1_1 TL5_4_1 YLc5_4_1_1 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint5_4_1 (i : Fin (realRepDim (5 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) i)) * T5_4_1
      = ((sgn (realRepBasisParity (5 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T5_4_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h0]; exact hinta5_4_1_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h1]; exact hinta5_4_1_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h2]; exact hinta5_4_1_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h3]; exact hinta5_4_1_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h4]; exact hinta5_4_1_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h5]; exact hinta5_4_1_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h6]; exact hinta5_4_1_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h7]; exact hinta5_4_1_7

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint5_4_1 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T5_4_1
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T5_4_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hintb5_4_1_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hintb5_4_1_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hintb5_4_1_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hintb5_4_1_3

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint5_4_1 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T5_4_1
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T5_4_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hintc5_4_1_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hintc5_4_1_1

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT5_4_1_mem_gInterSpace :
    gtOfT ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 T5_4_1 ∈ gInterSpace ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 hT5_4_1 hAint5_4_1 hBint5_4_1 hCint5_4_1

theorem gtOfT5_4_1_ne_zero : gtOfT ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 T5_4_1 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz5_4_1 T5_4_1_ne_zero

theorem gInterSpace5_4_1_ne_bot : gInterSpace ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT5_4_1_mem_gInterSpace, gtOfT5_4_1_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_5_4_1 : gParity ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) gInterSpace5_4_1_ne_bot).symm

end Triple_5_4_1

/-! ### The triple `(5,4,2)`

`gaugeSizeL = gaugeSizeR = (2,2)`, `dim D_3 = 8`, certgen parity `0`; the transported connector literal. -/
section Triple_5_4_2
open Module
theorem hsz5_4_2 : realGauge.gaugeSizeR 5 4 2 = realGauge.gaugeSizeL 5 4 2 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`4 x 4 x 8`). -/
def TL5_4_2 : List (List (List ℤ)) :=
  [[[1, 0, 0, 1, 0, 1, 1, 0], [-1, 0, 0, 1, 0, 1, -1, 0], [0, -1, 1, 0, -1, 0, 0, 1], [0, 1, 1, 0, -1, 0, 0, -1]],
   [[1, 0, 0, -1, 0, 1, -1, 0], [-1, 0, 0, -1, 0, 1, 1, 0], [0, -1, -1, 0, -1, 0, 0, -1], [0, 1, -1, 0, -1, 0, 0, 1]],
   [[0, 1, -1, 0, -1, 0, 0, 1], [0, 1, 1, 0, 1, 0, 0, 1], [1, 0, 0, 1, 0, -1, -1, 0], [1, 0, 0, -1, 0, 1, -1, 0]],
   [[0, -1, -1, 0, 1, 0, 0, 1], [0, -1, 1, 0, -1, 0, 0, 1], [-1, 0, 0, 1, 0, 1, -1, 0], [-1, 0, 0, -1, 0, -1, -1, 0]]]

/-- The same literal read at the composite frame `Fin 2 ⊕ Fin 2`. -/
noncomputable def Tc5_4_2 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet TL5_4_2 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_3`. -/
noncomputable def T5_4_2 : ((realGauge.D ((5 : ZMod 8) + 4 + 2)).matrixSuper
    (realGauge.gaugeSizeL 5 4 2).1 (realGauge.gaugeSizeL 5 4 2).2).carrier :=
  matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Tc5_4_2

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT5_4_2 : T5_4_2 ∈ ((realGauge.D ((5 : ZMod 8) + 4 + 2)).matrixSuper
    (realGauge.gaugeSizeL 5 4 2).1 (realGauge.gaugeSizeL 5 4 2).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((5 : ZMod 8) + 4 + 2) Tc5_4_2 0 (by decide)

theorem T5_4_2_ne_zero : T5_4_2 ≠ 0 :=
  matOfCoeff_ne_zero ((5 : ZMod 8) + 4 + 2) Tc5_4_2 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa5_4_2_0 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (2 : ZMod 8)).1 (realSize (4 : ZMod 8) (2 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I)
          * realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_6 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 2) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya5_4_2_0 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((5 : ZMod 8) + 4) (2 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa5_4_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa5_4_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca5_4_2_0 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_2_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_2_0 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_2_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_2_0 : ∀ I J g, Xa5_4_2_0 I J g = Xca5_4_2_0 I J g := by
  decide +kernel

theorem hYtaba5_4_2_0 : ∀ I J g, Ya5_4_2_0 I J g = Yca5_4_2_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta5_4_2_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_2
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xa5_4_2_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 hfuseZ_5_6 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xca5_4_2_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_2_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Ya5_4_2_0 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_5_4 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Yca5_4_2_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_2_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 5 4 2).1 (realGauge.gaugeSizeL 5 4 2).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_4_2_0 TL5_4_2 YLa5_4_2_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa5_4_2_1 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (2 : ZMod 8)).1 (realSize (4 : ZMod 8) (2 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I)
          * realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_6 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 2) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 2) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya5_4_2_1 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((5 : ZMod 8) + 4) (2 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa5_4_2_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa5_4_2_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, -1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca5_4_2_1 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_2_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_2_1 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_2_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_2_1 : ∀ I J g, Xa5_4_2_1 I J g = Xca5_4_2_1 I J g := by
  decide +kernel

theorem hYtaba5_4_2_1 : ∀ I J g, Ya5_4_2_1 I J g = Yca5_4_2_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta5_4_2_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_2
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xa5_4_2_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 hfuseZ_5_6 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xca5_4_2_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_2_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Ya5_4_2_1 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_5_4 hfuseZ_1_2 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Yca5_4_2_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_2_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 5 4 2).1 (realGauge.gaugeSizeL 5 4 2).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_4_2_1 TL5_4_2 YLa5_4_2_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa5_4_2_2 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (2 : ZMod 8)).1 (realSize (4 : ZMod 8) (2 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I)
          * realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_6 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 2) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 2) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya5_4_2_2 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((5 : ZMod 8) + 4) (2 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa5_4_2_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]],
   [[0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa5_4_2_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca5_4_2_2 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_2_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_2_2 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_2_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_2_2 : ∀ I J g, Xa5_4_2_2 I J g = Xca5_4_2_2 I J g := by
  decide +kernel

theorem hYtaba5_4_2_2 : ∀ I J g, Ya5_4_2_2 I J g = Yca5_4_2_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta5_4_2_2 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_2
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xa5_4_2_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 hfuseZ_5_6 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xca5_4_2_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_2_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Ya5_4_2_2 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_5_4 hfuseZ_1_2 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Yca5_4_2_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_2_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 5 4 2).1 (realGauge.gaugeSizeL 5 4 2).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_4_2_2 TL5_4_2 YLa5_4_2_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa5_4_2_3 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (2 : ZMod 8)).1 (realSize (4 : ZMod 8) (2 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I)
          * realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_6 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 2) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 2) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya5_4_2_3 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((5 : ZMod 8) + 4) (2 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa5_4_2_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa5_4_2_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0]],
   [[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca5_4_2_3 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_2_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_2_3 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_2_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_2_3 : ∀ I J g, Xa5_4_2_3 I J g = Xca5_4_2_3 I J g := by
  decide +kernel

theorem hYtaba5_4_2_3 : ∀ I J g, Ya5_4_2_3 I J g = Yca5_4_2_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta5_4_2_3 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_2
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xa5_4_2_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 hfuseZ_5_6 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xca5_4_2_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_2_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Ya5_4_2_3 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_5_4 hfuseZ_1_2 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Yca5_4_2_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_2_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 5 4 2).1 (realGauge.gaugeSizeL 5 4 2).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_4_2_3 TL5_4_2 YLa5_4_2_3 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Xa5_4_2_4 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (2 : ZMod 8)).1 (realSize (4 : ZMod 8) (2 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I)
          * realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_6 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 2) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 2) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Ya5_4_2_4 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((5 : ZMod 8) + 4) (2 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `4`, pre-tabulated. -/
def XLa5_4_2_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]],
   [[0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `4`, pre-tabulated. -/
def YLa5_4_2_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca5_4_2_4 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_2_4 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_2_4 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_2_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_2_4 : ∀ I J g, Xa5_4_2_4 I J g = Xca5_4_2_4 I J g := by
  decide +kernel

theorem hYtaba5_4_2_4 : ∀ I J g, Ya5_4_2_4 I J g = Yca5_4_2_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `4`** (Koszul sign `+1`). -/
theorem hinta5_4_2_4 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_2
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xa5_4_2_4 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 hfuseZ_5_6 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xca5_4_2_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_2_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Ya5_4_2_4 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_5_4 hfuseZ_1_2 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Yca5_4_2_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_2_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 5 4 2).1 (realGauge.gaugeSizeL 5 4 2).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_4_2_4 TL5_4_2 YLa5_4_2_4 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Xa5_4_2_5 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (2 : ZMod 8)).1 (realSize (4 : ZMod 8) (2 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I)
          * realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_6 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 2) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 2) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Ya5_4_2_5 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((5 : ZMod 8) + 4) (2 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `5`, pre-tabulated. -/
def XLa5_4_2_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, -1, 0]]]

/-- Left route at the `a`-slot generator `5`, pre-tabulated. -/
def YLa5_4_2_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, -1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca5_4_2_5 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_2_5 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_2_5 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_2_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_2_5 : ∀ I J g, Xa5_4_2_5 I J g = Xca5_4_2_5 I J g := by
  decide +kernel

theorem hYtaba5_4_2_5 : ∀ I J g, Ya5_4_2_5 I J g = Yca5_4_2_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `5`** (Koszul sign `+1`). -/
theorem hinta5_4_2_5 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_2
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xa5_4_2_5 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 hfuseZ_5_6 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xca5_4_2_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_2_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Ya5_4_2_5 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_5_4 hfuseZ_1_2 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Yca5_4_2_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_2_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 5 4 2).1 (realGauge.gaugeSizeL 5 4 2).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_4_2_5 TL5_4_2 YLa5_4_2_5 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Xa5_4_2_6 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (2 : ZMod 8)).1 (realSize (4 : ZMod 8) (2 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I)
          * realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_6 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 2) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 2) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Ya5_4_2_6 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((5 : ZMod 8) + 4) (2 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `6`, pre-tabulated. -/
def XLa5_4_2_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0]]]

/-- Left route at the `a`-slot generator `6`, pre-tabulated. -/
def YLa5_4_2_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca5_4_2_6 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_2_6 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_2_6 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_2_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_2_6 : ∀ I J g, Xa5_4_2_6 I J g = Xca5_4_2_6 I J g := by
  decide +kernel

theorem hYtaba5_4_2_6 : ∀ I J g, Ya5_4_2_6 I J g = Yca5_4_2_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `6`** (Koszul sign `+1`). -/
theorem hinta5_4_2_6 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_2
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xa5_4_2_6 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 hfuseZ_5_6 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xca5_4_2_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_2_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Ya5_4_2_6 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_5_4 hfuseZ_1_2 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Yca5_4_2_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_2_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 5 4 2).1 (realGauge.gaugeSizeL 5 4 2).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_4_2_6 TL5_4_2 YLa5_4_2_6 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Xa5_4_2_7 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (2 : ZMod 8)).1 (realSize (4 : ZMod 8) (2 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I)
          * realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_6 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 2) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 2) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Ya5_4_2_7 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((5 : ZMod 8) + 4) (2 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `7`, pre-tabulated. -/
def XLa5_4_2_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0]],
   [[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `7`, pre-tabulated. -/
def YLa5_4_2_7 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca5_4_2_7 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_2_7 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_2_7 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_2_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_2_7 : ∀ I J g, Xa5_4_2_7 I J g = Xca5_4_2_7 I J g := by
  decide +kernel

theorem hYtaba5_4_2_7 : ∀ I J g, Ya5_4_2_7 I J g = Yca5_4_2_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `7`** (Koszul sign `+1`). -/
theorem hinta5_4_2_7 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_2
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xa5_4_2_7 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 hfuseZ_5_6 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xca5_4_2_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_2_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Ya5_4_2_7 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_5_4 hfuseZ_1_2 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Yca5_4_2_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_2_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 5 4 2).1 (realGauge.gaugeSizeL 5 4 2).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_4_2_7 TL5_4_2 YLa5_4_2_7 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb5_4_2_0 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_6 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 2) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb5_4_2_0 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((5 : ZMod 8) + 4) (2 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb5_4_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb5_4_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb5_4_2_0 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb5_4_2_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_4_2_0 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb5_4_2_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_4_2_0 : ∀ I J g, Xb5_4_2_0 I J g = Xcb5_4_2_0 I J g := by
  decide +kernel

theorem hYtabb5_4_2_0 : ∀ I J g, Yb5_4_2_0 I J g = Ycb5_4_2_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb5_4_2_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T5_4_2
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xb5_4_2_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 hfuseZ_4_2 hfuseZ_5_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xcb5_4_2_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_4_2_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Yb5_4_2_0 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_5_4 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Ycb5_4_2_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_4_2_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 5 4 2).1 (realGauge.gaugeSizeL 5 4 2).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb5_4_2_0 TL5_4_2 YLb5_4_2_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb5_4_2_1 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_6 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 2) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb5_4_2_1 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((5 : ZMod 8) + 4) (2 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb5_4_2_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0]],
   [[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb5_4_2_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0]],
   [[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb5_4_2_1 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb5_4_2_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_4_2_1 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb5_4_2_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_4_2_1 : ∀ I J g, Xb5_4_2_1 I J g = Xcb5_4_2_1 I J g := by
  decide +kernel

theorem hYtabb5_4_2_1 : ∀ I J g, Yb5_4_2_1 I J g = Ycb5_4_2_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb5_4_2_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T5_4_2
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xb5_4_2_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 hfuseZ_4_2 hfuseZ_5_6 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xcb5_4_2_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_4_2_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Yb5_4_2_1 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_5_4 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Ycb5_4_2_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_4_2_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 5 4 2).1 (realGauge.gaugeSizeL 5 4 2).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb5_4_2_1 TL5_4_2 YLb5_4_2_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb5_4_2_2 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_6 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 2) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb5_4_2_2 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((5 : ZMod 8) + 4) (2 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb5_4_2_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb5_4_2_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb5_4_2_2 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb5_4_2_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_4_2_2 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb5_4_2_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_4_2_2 : ∀ I J g, Xb5_4_2_2 I J g = Xcb5_4_2_2 I J g := by
  decide +kernel

theorem hYtabb5_4_2_2 : ∀ I J g, Yb5_4_2_2 I J g = Ycb5_4_2_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb5_4_2_2 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T5_4_2
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xb5_4_2_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 hfuseZ_4_2 hfuseZ_5_6 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xcb5_4_2_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_4_2_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Yb5_4_2_2 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_5_4 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Ycb5_4_2_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_4_2_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 5 4 2).1 (realGauge.gaugeSizeL 5 4 2).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb5_4_2_2 TL5_4_2 YLb5_4_2_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb5_4_2_3 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_6 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 2) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb5_4_2_3 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((5 : ZMod 8) + 4) (2 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb5_4_2_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb5_4_2_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, -1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb5_4_2_3 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb5_4_2_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_4_2_3 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb5_4_2_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_4_2_3 : ∀ I J g, Xb5_4_2_3 I J g = Xcb5_4_2_3 I J g := by
  decide +kernel

theorem hYtabb5_4_2_3 : ∀ I J g, Yb5_4_2_3 I J g = Ycb5_4_2_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb5_4_2_3 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T5_4_2
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xb5_4_2_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 hfuseZ_4_2 hfuseZ_5_6 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xcb5_4_2_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_4_2_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Yb5_4_2_3 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_5_4 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Ycb5_4_2_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_4_2_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 5 4 2).1 (realGauge.gaugeSizeL 5 4 2).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb5_4_2_3 TL5_4_2 YLb5_4_2_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc5_4_2_0 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_6 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 2) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc5_4_2_0 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) = (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (4 : ZMod 8)).1 (realSize (5 : ZMod 8) (4 : ZMod 8)).2 (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_2 (fuseRow ((5 : ZMod 8) + 4) (2 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc5_4_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc5_4_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcc5_4_2_0 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc5_4_2_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_4_2_0 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc5_4_2_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_4_2_0 : ∀ I J g, Xc5_4_2_0 I J g = Xcc5_4_2_0 I J g := by
  decide +kernel

theorem hYtabc5_4_2_0 : ∀ I J g, Yc5_4_2_0 I J g = Ycc5_4_2_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc5_4_2_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T5_4_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xc5_4_2_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 hfuseZ_4_2 hfuseZ_5_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xcc5_4_2_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_4_2_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Yc5_4_2_0 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Ycc5_4_2_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_4_2_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 5 4 2).1 (realGauge.gaugeSizeL 5 4 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc5_4_2_0 TL5_4_2 YLc5_4_2_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc5_4_2_1 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_6 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 2) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc5_4_2_1 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) = (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (4 : ZMod 8)).1 (realSize (5 : ZMod 8) (4 : ZMod 8)).2 (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_2 (fuseRow ((5 : ZMod 8) + 4) (2 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc5_4_2_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc5_4_2_1 : List (List (List ℤ)) :=
  [[[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0, 0]]]

noncomputable def Xcc5_4_2_1 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc5_4_2_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_4_2_1 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc5_4_2_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_4_2_1 : ∀ I J g, Xc5_4_2_1 I J g = Xcc5_4_2_1 I J g := by
  decide +kernel

theorem hYtabc5_4_2_1 : ∀ I J g, Yc5_4_2_1 I J g = Ycc5_4_2_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc5_4_2_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T5_4_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xc5_4_2_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 hfuseZ_4_2 hfuseZ_5_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xcc5_4_2_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_4_2_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Yc5_4_2_1 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Ycc5_4_2_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_4_2_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 5 4 2).1 (realGauge.gaugeSizeL 5 4 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc5_4_2_1 TL5_4_2 YLc5_4_2_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc5_4_2_2 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_6 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 2) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc5_4_2_2 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) = (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (4 : ZMod 8)).1 (realSize (5 : ZMod 8) (4 : ZMod 8)).2 (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_2 (fuseRow ((5 : ZMod 8) + 4) (2 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc5_4_2_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc5_4_2_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0]]]

noncomputable def Xcc5_4_2_2 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc5_4_2_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_4_2_2 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc5_4_2_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_4_2_2 : ∀ I J g, Xc5_4_2_2 I J g = Xcc5_4_2_2 I J g := by
  decide +kernel

theorem hYtabc5_4_2_2 : ∀ I J g, Yc5_4_2_2 I J g = Ycc5_4_2_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc5_4_2_2 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T5_4_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xc5_4_2_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 hfuseZ_4_2 hfuseZ_5_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xcc5_4_2_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_4_2_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Yc5_4_2_2 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Ycc5_4_2_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_4_2_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 5 4 2).1 (realGauge.gaugeSizeL 5 4 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc5_4_2_2 TL5_4_2 YLc5_4_2_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc5_4_2_3 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) (ro (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_6 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 2) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 I) (ri (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc5_4_2_3 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) = (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (4 : ZMod 8)).1 (realSize (5 : ZMod 8) (4 : ZMod 8)).2 (lo (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_2 (fuseRow ((5 : ZMod 8) + 4) (2 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc5_4_2_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0]],
   [[0, 0, -1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc5_4_2_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]]]

noncomputable def Xcc5_4_2_3 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc5_4_2_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_4_2_3 : (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc5_4_2_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_4_2_3 : ∀ I J g, Xc5_4_2_3 I J g = Xcc5_4_2_3 I J g := by
  decide +kernel

theorem hYtabc5_4_2_3 : ∀ I J g, Yc5_4_2_3 I J g = Ycc5_4_2_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc5_4_2_3 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T5_4_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xc5_4_2_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 hfuseZ_4_2 hfuseZ_5_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Xcc5_4_2_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_4_2_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Yc5_4_2_3 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 2)) Ycc5_4_2_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 2).2)) (realRepBasis ((5 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_4_2_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 5 4 2).1 (realGauge.gaugeSizeL 5 4 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc5_4_2_3 TL5_4_2 YLc5_4_2_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint5_4_2 (i : Fin (realRepDim (5 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) i)) * T5_4_2
      = ((sgn (realRepBasisParity (5 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T5_4_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h0]; exact hinta5_4_2_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h1]; exact hinta5_4_2_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h2]; exact hinta5_4_2_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h3]; exact hinta5_4_2_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h4]; exact hinta5_4_2_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h5]; exact hinta5_4_2_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h6]; exact hinta5_4_2_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h7]; exact hinta5_4_2_7

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint5_4_2 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T5_4_2
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T5_4_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hintb5_4_2_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hintb5_4_2_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hintb5_4_2_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hintb5_4_2_3

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint5_4_2 (i : Fin (realRepDim (2 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) i)) * T5_4_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T5_4_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h0]; exact hintc5_4_2_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h1]; exact hintc5_4_2_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h2]; exact hintc5_4_2_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h3]; exact hintc5_4_2_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT5_4_2_mem_gInterSpace :
    gtOfT ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 T5_4_2 ∈ gInterSpace ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 hT5_4_2 hAint5_4_2 hBint5_4_2 hCint5_4_2

theorem gtOfT5_4_2_ne_zero : gtOfT ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 T5_4_2 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz5_4_2 T5_4_2_ne_zero

theorem gInterSpace5_4_2_ne_bot : gInterSpace ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT5_4_2_mem_gInterSpace, gtOfT5_4_2_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_5_4_2 : gParity ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) gInterSpace5_4_2_ne_bot).symm

end Triple_5_4_2

/-! ### The triple `(5,4,6)`

`gaugeSizeL = gaugeSizeR = (4,4)`, `dim D_7 = 2`, certgen parity `0`; the transported connector literal. -/
section Triple_5_4_6
open Module
theorem hsz5_4_6 : realGauge.gaugeSizeR 5 4 6 = realGauge.gaugeSizeL 5 4 6 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`8 x 8 x 2`). -/
def TL5_4_6 : List (List (List ℤ)) :=
  [[[0, 0], [-1, 0], [1, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, -1]],
   [[-1, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, -1], [0, -1], [0, 0]],
   [[0, 0], [1, 0], [1, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, -1]],
   [[1, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 1], [0, -1], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 1], [0, 0], [1, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 1], [0, 0], [1, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 1], [0, 0], [-1, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 1], [0, 0], [-1, 0], [0, 0], [0, 0], [1, 0]]]

/-- The same literal read at the composite frame `Fin 4 ⊕ Fin 4`. -/
noncomputable def Tc5_4_6 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet TL5_4_6 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_7`. -/
noncomputable def T5_4_6 : ((realGauge.D ((5 : ZMod 8) + 4 + 6)).matrixSuper
    (realGauge.gaugeSizeL 5 4 6).1 (realGauge.gaugeSizeL 5 4 6).2).carrier :=
  matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Tc5_4_6

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT5_4_6 : T5_4_6 ∈ ((realGauge.D ((5 : ZMod 8) + 4 + 6)).matrixSuper
    (realGauge.gaugeSizeL 5 4 6).1 (realGauge.gaugeSizeL 5 4 6).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((5 : ZMod 8) + 4 + 6) Tc5_4_6 0 (by decide)

theorem T5_4_6_ne_zero : T5_4_6 ≠ 0 :=
  matOfCoeff_ne_zero ((5 : ZMod 8) + 4 + 6) Tc5_4_6 (Sum.inl ⟨0, by decide⟩) (Sum.inr ⟨0, by decide⟩) ⟨1, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa5_4_6_0 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (6 : ZMod 8)).1 (realSize (4 : ZMod 8) (6 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I)
          * realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 6) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya5_4_6_0 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((5 : ZMod 8) + 4) (6 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa5_4_6_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa5_4_6_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xca5_4_6_0 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_6_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_6_0 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_6_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_6_0 : ∀ I J g, Xa5_4_6_0 I J g = Xca5_4_6_0 I J g := by
  decide +kernel

theorem hYtaba5_4_6_0 : ∀ I J g, Ya5_4_6_0 I J g = Yca5_4_6_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta5_4_6_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_6
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_6 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xa5_4_6_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xca5_4_6_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_6_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Ya5_4_6_0 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hfuseZ_5_4 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Yca5_4_6_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_6_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 6) (realGauge.gaugeSizeL 5 4 6).1 (realGauge.gaugeSizeL 5 4 6).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_4_6_0 TL5_4_6 YLa5_4_6_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa5_4_6_1 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (6 : ZMod 8)).1 (realSize (4 : ZMod 8) (6 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I)
          * realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 6) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 6) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya5_4_6_1 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((5 : ZMod 8) + 4) (6 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa5_4_6_1 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa5_4_6_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca5_4_6_1 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_6_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_6_1 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_6_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_6_1 : ∀ I J g, Xa5_4_6_1 I J g = Xca5_4_6_1 I J g := by
  decide +kernel

theorem hYtaba5_4_6_1 : ∀ I J g, Ya5_4_6_1 I J g = Yca5_4_6_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta5_4_6_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_6
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_6 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xa5_4_6_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 hfuseZ_5_2 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xca5_4_6_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_6_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Ya5_4_6_1 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hfuseZ_5_4 hfuseZ_1_6 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Yca5_4_6_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_6_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 6) (realGauge.gaugeSizeL 5 4 6).1 (realGauge.gaugeSizeL 5 4 6).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_4_6_1 TL5_4_6 YLa5_4_6_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa5_4_6_2 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (6 : ZMod 8)).1 (realSize (4 : ZMod 8) (6 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I)
          * realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 6) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 6) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya5_4_6_2 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((5 : ZMod 8) + 4) (6 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa5_4_6_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa5_4_6_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca5_4_6_2 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_6_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_6_2 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_6_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_6_2 : ∀ I J g, Xa5_4_6_2 I J g = Xca5_4_6_2 I J g := by
  decide +kernel

theorem hYtaba5_4_6_2 : ∀ I J g, Ya5_4_6_2 I J g = Yca5_4_6_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta5_4_6_2 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_6
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_6 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xa5_4_6_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 hfuseZ_5_2 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xca5_4_6_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_6_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Ya5_4_6_2 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hfuseZ_5_4 hfuseZ_1_6 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Yca5_4_6_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_6_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 6) (realGauge.gaugeSizeL 5 4 6).1 (realGauge.gaugeSizeL 5 4 6).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_4_6_2 TL5_4_6 YLa5_4_6_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa5_4_6_3 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (6 : ZMod 8)).1 (realSize (4 : ZMod 8) (6 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I)
          * realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 6) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 6) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya5_4_6_3 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((5 : ZMod 8) + 4) (6 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa5_4_6_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa5_4_6_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]]]

noncomputable def Xca5_4_6_3 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_6_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_6_3 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_6_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_6_3 : ∀ I J g, Xa5_4_6_3 I J g = Xca5_4_6_3 I J g := by
  decide +kernel

theorem hYtaba5_4_6_3 : ∀ I J g, Ya5_4_6_3 I J g = Yca5_4_6_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta5_4_6_3 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_6
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_6 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xa5_4_6_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 hfuseZ_5_2 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xca5_4_6_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_6_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Ya5_4_6_3 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hfuseZ_5_4 hfuseZ_1_6 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Yca5_4_6_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_6_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 6) (realGauge.gaugeSizeL 5 4 6).1 (realGauge.gaugeSizeL 5 4 6).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_4_6_3 TL5_4_6 YLa5_4_6_3 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Xa5_4_6_4 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (6 : ZMod 8)).1 (realSize (4 : ZMod 8) (6 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I)
          * realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 6) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 6) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Ya5_4_6_4 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((5 : ZMod 8) + 4) (6 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `4`, pre-tabulated. -/
def XLa5_4_6_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `4`, pre-tabulated. -/
def YLa5_4_6_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca5_4_6_4 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_6_4 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_6_4 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_6_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_6_4 : ∀ I J g, Xa5_4_6_4 I J g = Xca5_4_6_4 I J g := by
  decide +kernel

theorem hYtaba5_4_6_4 : ∀ I J g, Ya5_4_6_4 I J g = Yca5_4_6_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `4`** (Koszul sign `+1`). -/
theorem hinta5_4_6_4 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_6
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_6 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xa5_4_6_4 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 hfuseZ_5_2 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xca5_4_6_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_6_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Ya5_4_6_4 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hfuseZ_5_4 hfuseZ_1_6 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Yca5_4_6_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_6_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 6) (realGauge.gaugeSizeL 5 4 6).1 (realGauge.gaugeSizeL 5 4 6).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_4_6_4 TL5_4_6 YLa5_4_6_4 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Xa5_4_6_5 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (6 : ZMod 8)).1 (realSize (4 : ZMod 8) (6 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I)
          * realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 6) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 6) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Ya5_4_6_5 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((5 : ZMod 8) + 4) (6 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `5`, pre-tabulated. -/
def XLa5_4_6_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `5`, pre-tabulated. -/
def YLa5_4_6_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca5_4_6_5 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_6_5 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_6_5 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_6_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_6_5 : ∀ I J g, Xa5_4_6_5 I J g = Xca5_4_6_5 I J g := by
  decide +kernel

theorem hYtaba5_4_6_5 : ∀ I J g, Ya5_4_6_5 I J g = Yca5_4_6_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `5`** (Koszul sign `+1`). -/
theorem hinta5_4_6_5 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_6
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_6 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xa5_4_6_5 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 hfuseZ_5_2 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xca5_4_6_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_6_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Ya5_4_6_5 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hfuseZ_5_4 hfuseZ_1_6 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Yca5_4_6_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_6_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 6) (realGauge.gaugeSizeL 5 4 6).1 (realGauge.gaugeSizeL 5 4 6).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_4_6_5 TL5_4_6 YLa5_4_6_5 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Xa5_4_6_6 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (6 : ZMod 8)).1 (realSize (4 : ZMod 8) (6 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I)
          * realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 6) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 6) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Ya5_4_6_6 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((5 : ZMod 8) + 4) (6 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `6`, pre-tabulated. -/
def XLa5_4_6_6 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `6`, pre-tabulated. -/
def YLa5_4_6_6 : List (List (List ℤ)) :=
  [[[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]]]

noncomputable def Xca5_4_6_6 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_6_6 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_6_6 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_6_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_6_6 : ∀ I J g, Xa5_4_6_6 I J g = Xca5_4_6_6 I J g := by
  decide +kernel

theorem hYtaba5_4_6_6 : ∀ I J g, Ya5_4_6_6 I J g = Yca5_4_6_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `6`** (Koszul sign `+1`). -/
theorem hinta5_4_6_6 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_6
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_6 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xa5_4_6_6 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 hfuseZ_5_2 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xca5_4_6_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_6_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Ya5_4_6_6 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hfuseZ_5_4 hfuseZ_1_6 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Yca5_4_6_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_6_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 6) (realGauge.gaugeSizeL 5 4 6).1 (realGauge.gaugeSizeL 5 4 6).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_4_6_6 TL5_4_6 YLa5_4_6_6 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Xa5_4_6_7 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (6 : ZMod 8)).1 (realSize (4 : ZMod 8) (6 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I)
          * realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 6) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 6) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Ya5_4_6_7 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((5 : ZMod 8) + 4) (6 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `7`, pre-tabulated. -/
def XLa5_4_6_7 : List (List (List ℤ)) :=
  [[[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]]]

/-- Left route at the `a`-slot generator `7`, pre-tabulated. -/
def YLa5_4_6_7 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca5_4_6_7 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_6_7 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_6_7 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_6_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_6_7 : ∀ I J g, Xa5_4_6_7 I J g = Xca5_4_6_7 I J g := by
  decide +kernel

theorem hYtaba5_4_6_7 : ∀ I J g, Ya5_4_6_7 I J g = Yca5_4_6_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `7`** (Koszul sign `+1`). -/
theorem hinta5_4_6_7 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_6
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_6 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xa5_4_6_7 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 hfuseZ_5_2 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xca5_4_6_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_6_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Ya5_4_6_7 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hfuseZ_5_4 hfuseZ_1_6 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Yca5_4_6_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_6_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 6) (realGauge.gaugeSizeL 5 4 6).1 (realGauge.gaugeSizeL 5 4 6).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_4_6_7 TL5_4_6 YLa5_4_6_7 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb5_4_6_0 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_6 (fuseRow (4 : ZMod 8) (6 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) ee) (fuseCol (4 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 6) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb5_4_6_0 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((5 : ZMod 8) + 4) (6 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb5_4_6_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb5_4_6_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcb5_4_6_0 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb5_4_6_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_4_6_0 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb5_4_6_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_4_6_0 : ∀ I J g, Xb5_4_6_0 I J g = Xcb5_4_6_0 I J g := by
  decide +kernel

theorem hYtabb5_4_6_0 : ∀ I J g, Yb5_4_6_0 I J g = Ycb5_4_6_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb5_4_6_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T5_4_6
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_6 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xb5_4_6_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 hfuseZ_4_6 hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xcb5_4_6_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_4_6_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Yb5_4_6_0 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hfuseZ_5_4 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Ycb5_4_6_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_4_6_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 6) (realGauge.gaugeSizeL 5 4 6).1 (realGauge.gaugeSizeL 5 4 6).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb5_4_6_0 TL5_4_6 YLb5_4_6_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb5_4_6_1 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_6 (fuseRow (4 : ZMod 8) (6 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) ee) (fuseCol (4 : ZMod 8) (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 6) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb5_4_6_1 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((5 : ZMod 8) + 4) (6 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb5_4_6_1 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb5_4_6_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]]]

noncomputable def Xcb5_4_6_1 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb5_4_6_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_4_6_1 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb5_4_6_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_4_6_1 : ∀ I J g, Xb5_4_6_1 I J g = Xcb5_4_6_1 I J g := by
  decide +kernel

theorem hYtabb5_4_6_1 : ∀ I J g, Yb5_4_6_1 I J g = Ycb5_4_6_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb5_4_6_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T5_4_6
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_6 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xb5_4_6_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 hfuseZ_4_6 hfuseZ_5_2 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xcb5_4_6_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_4_6_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Yb5_4_6_1 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hfuseZ_5_4 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Ycb5_4_6_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_4_6_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 6) (realGauge.gaugeSizeL 5 4 6).1 (realGauge.gaugeSizeL 5 4 6).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb5_4_6_1 TL5_4_6 YLb5_4_6_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb5_4_6_2 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_6 (fuseRow (4 : ZMod 8) (6 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) ee) (fuseCol (4 : ZMod 8) (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 6) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb5_4_6_2 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((5 : ZMod 8) + 4) (6 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb5_4_6_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb5_4_6_2 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]]]

noncomputable def Xcb5_4_6_2 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb5_4_6_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_4_6_2 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb5_4_6_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_4_6_2 : ∀ I J g, Xb5_4_6_2 I J g = Xcb5_4_6_2 I J g := by
  decide +kernel

theorem hYtabb5_4_6_2 : ∀ I J g, Yb5_4_6_2 I J g = Ycb5_4_6_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb5_4_6_2 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T5_4_6
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_6 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xb5_4_6_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 hfuseZ_4_6 hfuseZ_5_2 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xcb5_4_6_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_4_6_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Yb5_4_6_2 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hfuseZ_5_4 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Ycb5_4_6_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_4_6_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 6) (realGauge.gaugeSizeL 5 4 6).1 (realGauge.gaugeSizeL 5 4 6).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb5_4_6_2 TL5_4_6 YLb5_4_6_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb5_4_6_3 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_6 (fuseRow (4 : ZMod 8) (6 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) ee) (fuseCol (4 : ZMod 8) (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 6) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb5_4_6_3 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((5 : ZMod 8) + 4) (6 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb5_4_6_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb5_4_6_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb5_4_6_3 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb5_4_6_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_4_6_3 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb5_4_6_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_4_6_3 : ∀ I J g, Xb5_4_6_3 I J g = Xcb5_4_6_3 I J g := by
  decide +kernel

theorem hYtabb5_4_6_3 : ∀ I J g, Yb5_4_6_3 I J g = Ycb5_4_6_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb5_4_6_3 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T5_4_6
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_6 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xb5_4_6_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 hfuseZ_4_6 hfuseZ_5_2 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xcb5_4_6_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_4_6_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Yb5_4_6_3 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hfuseZ_5_4 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Ycb5_4_6_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_4_6_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 6) (realGauge.gaugeSizeL 5 4 6).1 (realGauge.gaugeSizeL 5 4 6).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb5_4_6_3 TL5_4_6 YLb5_4_6_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc5_4_6_0 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_6 (fuseRow (4 : ZMod 8) (6 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) ee) (fuseCol (4 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 6) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc5_4_6_0 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) = (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (4 : ZMod 8)).1 (realSize (5 : ZMod 8) (4 : ZMod 8)).2 (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_6 (fuseRow ((5 : ZMod 8) + 4) (6 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc5_4_6_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc5_4_6_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcc5_4_6_0 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc5_4_6_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_4_6_0 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc5_4_6_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_4_6_0 : ∀ I J g, Xc5_4_6_0 I J g = Xcc5_4_6_0 I J g := by
  decide +kernel

theorem hYtabc5_4_6_0 : ∀ I J g, Yc5_4_6_0 I J g = Ycc5_4_6_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc5_4_6_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T5_4_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_6 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xc5_4_6_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 hfuseZ_4_6 hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xcc5_4_6_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_4_6_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Yc5_4_6_0 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Ycc5_4_6_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_4_6_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 6) (realGauge.gaugeSizeL 5 4 6).1 (realGauge.gaugeSizeL 5 4 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc5_4_6_0 TL5_4_6 YLc5_4_6_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc5_4_6_1 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_6 (fuseRow (4 : ZMod 8) (6 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) ee) (fuseCol (4 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 6) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc5_4_6_1 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) = (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (4 : ZMod 8)).1 (realSize (5 : ZMod 8) (4 : ZMod 8)).2 (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_6 (fuseRow ((5 : ZMod 8) + 4) (6 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc5_4_6_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc5_4_6_1 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]]]

noncomputable def Xcc5_4_6_1 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc5_4_6_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_4_6_1 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc5_4_6_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_4_6_1 : ∀ I J g, Xc5_4_6_1 I J g = Xcc5_4_6_1 I J g := by
  decide +kernel

theorem hYtabc5_4_6_1 : ∀ I J g, Yc5_4_6_1 I J g = Ycc5_4_6_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc5_4_6_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T5_4_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_6 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xc5_4_6_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 hfuseZ_4_6 hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xcc5_4_6_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_4_6_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Yc5_4_6_1 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Ycc5_4_6_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_4_6_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 6) (realGauge.gaugeSizeL 5 4 6).1 (realGauge.gaugeSizeL 5 4 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc5_4_6_1 TL5_4_6 YLc5_4_6_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc5_4_6_2 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_6 (fuseRow (4 : ZMod 8) (6 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) ee) (fuseCol (4 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 6) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc5_4_6_2 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) = (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (4 : ZMod 8)).1 (realSize (5 : ZMod 8) (4 : ZMod 8)).2 (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_6 (fuseRow ((5 : ZMod 8) + 4) (6 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc5_4_6_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc5_4_6_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc5_4_6_2 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc5_4_6_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_4_6_2 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc5_4_6_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_4_6_2 : ∀ I J g, Xc5_4_6_2 I J g = Xcc5_4_6_2 I J g := by
  decide +kernel

theorem hYtabc5_4_6_2 : ∀ I J g, Yc5_4_6_2 I J g = Ycc5_4_6_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc5_4_6_2 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T5_4_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_6 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xc5_4_6_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 hfuseZ_4_6 hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xcc5_4_6_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_4_6_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Yc5_4_6_2 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Ycc5_4_6_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_4_6_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 6) (realGauge.gaugeSizeL 5 4 6).1 (realGauge.gaugeSizeL 5 4 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc5_4_6_2 TL5_4_6 YLc5_4_6_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc5_4_6_3 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_6 (fuseRow (4 : ZMod 8) (6 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) (ro (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) ee) (fuseCol (4 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 6) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 I) (ri (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc5_4_6_3 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) = (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (4 : ZMod 8)).1 (realSize (5 : ZMod 8) (4 : ZMod 8)).2 (lo (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_6 (fuseRow ((5 : ZMod 8) + 4) (6 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc5_4_6_3 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc5_4_6_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc5_4_6_3 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc5_4_6_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_4_6_3 : (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc5_4_6_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_4_6_3 : ∀ I J g, Xc5_4_6_3 I J g = Xcc5_4_6_3 I J g := by
  decide +kernel

theorem hYtabc5_4_6_3 : ∀ I J g, Yc5_4_6_3 I J g = Ycc5_4_6_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc5_4_6_3 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T5_4_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_6 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xc5_4_6_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 hfuseZ_4_6 hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Xcc5_4_6_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_4_6_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Yc5_4_6_3 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 6)) Ycc5_4_6_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 6).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 6).2)) (realRepBasis ((5 : ZMod 8) + 4 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_4_6_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 6) (realGauge.gaugeSizeL 5 4 6).1 (realGauge.gaugeSizeL 5 4 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc5_4_6_3 TL5_4_6 YLc5_4_6_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint5_4_6 (i : Fin (realRepDim (5 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) i)) * T5_4_6
      = ((sgn (realRepBasisParity (5 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T5_4_6 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h0]; exact hinta5_4_6_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h1]; exact hinta5_4_6_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h2]; exact hinta5_4_6_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h3]; exact hinta5_4_6_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h4]; exact hinta5_4_6_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h5]; exact hinta5_4_6_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h6]; exact hinta5_4_6_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h7]; exact hinta5_4_6_7

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint5_4_6 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T5_4_6
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T5_4_6 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hintb5_4_6_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hintb5_4_6_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hintb5_4_6_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hintb5_4_6_3

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint5_4_6 (i : Fin (realRepDim (6 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) i)) * T5_4_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T5_4_6 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h0]; exact hintc5_4_6_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h1]; exact hintc5_4_6_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h2]; exact hintc5_4_6_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h3]; exact hintc5_4_6_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT5_4_6_mem_gInterSpace :
    gtOfT ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 T5_4_6 ∈ gInterSpace ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 hT5_4_6 hAint5_4_6 hBint5_4_6 hCint5_4_6

theorem gtOfT5_4_6_ne_zero : gtOfT ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 T5_4_6 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) hsz5_4_6 T5_4_6_ne_zero

theorem gInterSpace5_4_6_ne_bot : gInterSpace ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT5_4_6_mem_gInterSpace, gtOfT5_4_6_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_5_4_6 : gParity ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (6 : ZMod 8) gInterSpace5_4_6_ne_bot).symm

end Triple_5_4_6

/-! ### The triple `(5,4,7)`

`gaugeSizeL = gaugeSizeR = (4,4)`, `dim D_0 = 1`, certgen parity `0`; the transported connector literal. -/
section Triple_5_4_7
open Module
theorem hsz5_4_7 : realGauge.gaugeSizeR 5 4 7 = realGauge.gaugeSizeL 5 4 7 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`8 x 8 x 1`). -/
def TL5_4_7 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

/-- The same literal read at the composite frame `Fin 4 ⊕ Fin 4`. -/
noncomputable def Tc5_4_7 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet TL5_4_7 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_0`. -/
noncomputable def T5_4_7 : ((realGauge.D ((5 : ZMod 8) + 4 + 7)).matrixSuper
    (realGauge.gaugeSizeL 5 4 7).1 (realGauge.gaugeSizeL 5 4 7).2).carrier :=
  matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Tc5_4_7

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT5_4_7 : T5_4_7 ∈ ((realGauge.D ((5 : ZMod 8) + 4 + 7)).matrixSuper
    (realGauge.gaugeSizeL 5 4 7).1 (realGauge.gaugeSizeL 5 4 7).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((5 : ZMod 8) + 4 + 7) Tc5_4_7 0 (by decide)

theorem T5_4_7_ne_zero : T5_4_7 ≠ 0 :=
  matOfCoeff_ne_zero ((5 : ZMod 8) + 4 + 7) Tc5_4_7 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨2, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa5_4_7_0 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (7 : ZMod 8)).1 (realSize (4 : ZMod 8) (7 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I)
          * realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 7) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya5_4_7_0 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((5 : ZMod 8) + 4) (7 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa5_4_7_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa5_4_7_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xca5_4_7_0 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_7_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_7_0 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_7_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_7_0 : ∀ I J g, Xa5_4_7_0 I J g = Xca5_4_7_0 I J g := by
  decide +kernel

theorem hYtaba5_4_7_0 : ∀ I J g, Ya5_4_7_0 I J g = Yca5_4_7_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta5_4_7_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_7
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_7 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xa5_4_7_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xca5_4_7_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_7_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Ya5_4_7_0 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hfuseZ_5_4 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Yca5_4_7_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_7_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 7) (realGauge.gaugeSizeL 5 4 7).1 (realGauge.gaugeSizeL 5 4 7).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_4_7_0 TL5_4_7 YLa5_4_7_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa5_4_7_1 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (7 : ZMod 8)).1 (realSize (4 : ZMod 8) (7 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I)
          * realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 7) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 7) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya5_4_7_1 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((5 : ZMod 8) + 4) (7 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa5_4_7_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa5_4_7_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]]]

noncomputable def Xca5_4_7_1 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_7_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_7_1 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_7_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_7_1 : ∀ I J g, Xa5_4_7_1 I J g = Xca5_4_7_1 I J g := by
  decide +kernel

theorem hYtaba5_4_7_1 : ∀ I J g, Ya5_4_7_1 I J g = Yca5_4_7_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta5_4_7_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_7
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_7 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xa5_4_7_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 hfuseZ_5_3 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xca5_4_7_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_7_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Ya5_4_7_1 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hfuseZ_5_4 hfuseZ_1_7 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Yca5_4_7_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_7_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 7) (realGauge.gaugeSizeL 5 4 7).1 (realGauge.gaugeSizeL 5 4 7).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_4_7_1 TL5_4_7 YLa5_4_7_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa5_4_7_2 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (7 : ZMod 8)).1 (realSize (4 : ZMod 8) (7 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I)
          * realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 7) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 7) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya5_4_7_2 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((5 : ZMod 8) + 4) (7 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa5_4_7_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa5_4_7_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xca5_4_7_2 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_7_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_7_2 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_7_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_7_2 : ∀ I J g, Xa5_4_7_2 I J g = Xca5_4_7_2 I J g := by
  decide +kernel

theorem hYtaba5_4_7_2 : ∀ I J g, Ya5_4_7_2 I J g = Yca5_4_7_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta5_4_7_2 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_7
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_7 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xa5_4_7_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 hfuseZ_5_3 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xca5_4_7_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_7_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Ya5_4_7_2 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hfuseZ_5_4 hfuseZ_1_7 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Yca5_4_7_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_7_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 7) (realGauge.gaugeSizeL 5 4 7).1 (realGauge.gaugeSizeL 5 4 7).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_4_7_2 TL5_4_7 YLa5_4_7_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa5_4_7_3 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (7 : ZMod 8)).1 (realSize (4 : ZMod 8) (7 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I)
          * realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 7) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 7) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya5_4_7_3 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((5 : ZMod 8) + 4) (7 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa5_4_7_3 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa5_4_7_3 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]]]

noncomputable def Xca5_4_7_3 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_7_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_7_3 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_7_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_7_3 : ∀ I J g, Xa5_4_7_3 I J g = Xca5_4_7_3 I J g := by
  decide +kernel

theorem hYtaba5_4_7_3 : ∀ I J g, Ya5_4_7_3 I J g = Yca5_4_7_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta5_4_7_3 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_7
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_7 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xa5_4_7_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 hfuseZ_5_3 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xca5_4_7_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_7_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Ya5_4_7_3 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hfuseZ_5_4 hfuseZ_1_7 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Yca5_4_7_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_7_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 7) (realGauge.gaugeSizeL 5 4 7).1 (realGauge.gaugeSizeL 5 4 7).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_4_7_3 TL5_4_7 YLa5_4_7_3 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Xa5_4_7_4 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (7 : ZMod 8)).1 (realSize (4 : ZMod 8) (7 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I)
          * realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 7) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 7) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Ya5_4_7_4 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((5 : ZMod 8) + 4) (7 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `4`, pre-tabulated. -/
def XLa5_4_7_4 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `4`, pre-tabulated. -/
def YLa5_4_7_4 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xca5_4_7_4 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_7_4 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_7_4 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_7_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_7_4 : ∀ I J g, Xa5_4_7_4 I J g = Xca5_4_7_4 I J g := by
  decide +kernel

theorem hYtaba5_4_7_4 : ∀ I J g, Ya5_4_7_4 I J g = Yca5_4_7_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `4`** (Koszul sign `+1`). -/
theorem hinta5_4_7_4 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_7
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_7 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xa5_4_7_4 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 hfuseZ_5_3 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xca5_4_7_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_7_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Ya5_4_7_4 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hfuseZ_5_4 hfuseZ_1_7 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Yca5_4_7_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_7_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 7) (realGauge.gaugeSizeL 5 4 7).1 (realGauge.gaugeSizeL 5 4 7).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_4_7_4 TL5_4_7 YLa5_4_7_4 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Xa5_4_7_5 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (7 : ZMod 8)).1 (realSize (4 : ZMod 8) (7 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I)
          * realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 7) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 7) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Ya5_4_7_5 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((5 : ZMod 8) + 4) (7 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `5`, pre-tabulated. -/
def XLa5_4_7_5 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]]]

/-- Left route at the `a`-slot generator `5`, pre-tabulated. -/
def YLa5_4_7_5 : List (List (List ℤ)) :=
  [[[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

noncomputable def Xca5_4_7_5 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_7_5 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_7_5 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_7_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_7_5 : ∀ I J g, Xa5_4_7_5 I J g = Xca5_4_7_5 I J g := by
  decide +kernel

theorem hYtaba5_4_7_5 : ∀ I J g, Ya5_4_7_5 I J g = Yca5_4_7_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `5`** (Koszul sign `+1`). -/
theorem hinta5_4_7_5 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_7
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_7 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xa5_4_7_5 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 hfuseZ_5_3 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xca5_4_7_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_7_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Ya5_4_7_5 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hfuseZ_5_4 hfuseZ_1_7 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Yca5_4_7_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_7_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 7) (realGauge.gaugeSizeL 5 4 7).1 (realGauge.gaugeSizeL 5 4 7).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_4_7_5 TL5_4_7 YLa5_4_7_5 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Xa5_4_7_6 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (7 : ZMod 8)).1 (realSize (4 : ZMod 8) (7 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I)
          * realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 7) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 7) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Ya5_4_7_6 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((5 : ZMod 8) + 4) (7 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `6`, pre-tabulated. -/
def XLa5_4_7_6 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `6`, pre-tabulated. -/
def YLa5_4_7_6 : List (List (List ℤ)) :=
  [[[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]]]

noncomputable def Xca5_4_7_6 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_7_6 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_7_6 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_7_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_7_6 : ∀ I J g, Xa5_4_7_6 I J g = Xca5_4_7_6 I J g := by
  decide +kernel

theorem hYtaba5_4_7_6 : ∀ I J g, Ya5_4_7_6 I J g = Yca5_4_7_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `6`** (Koszul sign `+1`). -/
theorem hinta5_4_7_6 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_7
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_7 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xa5_4_7_6 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 hfuseZ_5_3 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xca5_4_7_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_7_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Ya5_4_7_6 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hfuseZ_5_4 hfuseZ_1_7 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Yca5_4_7_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_7_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 7) (realGauge.gaugeSizeL 5 4 7).1 (realGauge.gaugeSizeL 5 4 7).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_4_7_6 TL5_4_7 YLa5_4_7_6 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Xa5_4_7_7 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) = (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (7 : ZMod 8)).1 (realSize (4 : ZMod 8) (7 : ZMod 8)).2 (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I)
          * realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 7) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 7) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Ya5_4_7_7 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((5 : ZMod 8) + 4) (7 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `7`, pre-tabulated. -/
def XLa5_4_7_7 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `7`, pre-tabulated. -/
def YLa5_4_7_7 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]]]

noncomputable def Xca5_4_7_7 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa5_4_7_7 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_4_7_7 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa5_4_7_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_4_7_7 : ∀ I J g, Xa5_4_7_7 I J g = Xca5_4_7_7 I J g := by
  decide +kernel

theorem hYtaba5_4_7_7 : ∀ I J g, Ya5_4_7_7 I J g = Yca5_4_7_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `7`** (Koszul sign `+1`). -/
theorem hinta5_4_7_7 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_4_7
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_7 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xa5_4_7_7 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 hfuseZ_5_3 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xca5_4_7_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_4_7_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Ya5_4_7_7 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hfuseZ_5_4 hfuseZ_1_7 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Yca5_4_7_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_4_7_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 7) (realGauge.gaugeSizeL 5 4 7).1 (realGauge.gaugeSizeL 5 4 7).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_4_7_7 TL5_4_7 YLa5_4_7_7 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb5_4_7_0 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_7 (fuseRow (4 : ZMod 8) (7 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) ee) (fuseCol (4 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 7) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb5_4_7_0 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((5 : ZMod 8) + 4) (7 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb5_4_7_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb5_4_7_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xcb5_4_7_0 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb5_4_7_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_4_7_0 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb5_4_7_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_4_7_0 : ∀ I J g, Xb5_4_7_0 I J g = Xcb5_4_7_0 I J g := by
  decide +kernel

theorem hYtabb5_4_7_0 : ∀ I J g, Yb5_4_7_0 I J g = Ycb5_4_7_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb5_4_7_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T5_4_7
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_7 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xb5_4_7_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 hfuseZ_4_7 hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xcb5_4_7_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_4_7_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Yb5_4_7_0 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hfuseZ_5_4 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Ycb5_4_7_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_4_7_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 7) (realGauge.gaugeSizeL 5 4 7).1 (realGauge.gaugeSizeL 5 4 7).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb5_4_7_0 TL5_4_7 YLb5_4_7_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb5_4_7_1 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_7 (fuseRow (4 : ZMod 8) (7 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) ee) (fuseCol (4 : ZMod 8) (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 7) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb5_4_7_1 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((5 : ZMod 8) + 4) (7 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb5_4_7_1 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb5_4_7_1 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]]]

noncomputable def Xcb5_4_7_1 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb5_4_7_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_4_7_1 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb5_4_7_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_4_7_1 : ∀ I J g, Xb5_4_7_1 I J g = Xcb5_4_7_1 I J g := by
  decide +kernel

theorem hYtabb5_4_7_1 : ∀ I J g, Yb5_4_7_1 I J g = Ycb5_4_7_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb5_4_7_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T5_4_7
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_7 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xb5_4_7_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 hfuseZ_4_7 hfuseZ_5_3 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xcb5_4_7_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_4_7_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Yb5_4_7_1 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hfuseZ_5_4 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Ycb5_4_7_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_4_7_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 7) (realGauge.gaugeSizeL 5 4 7).1 (realGauge.gaugeSizeL 5 4 7).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb5_4_7_1 TL5_4_7 YLb5_4_7_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb5_4_7_2 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_7 (fuseRow (4 : ZMod 8) (7 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) ee) (fuseCol (4 : ZMod 8) (7 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 7) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb5_4_7_2 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((5 : ZMod 8) + 4) (7 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb5_4_7_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb5_4_7_2 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]]]

noncomputable def Xcb5_4_7_2 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb5_4_7_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_4_7_2 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb5_4_7_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_4_7_2 : ∀ I J g, Xb5_4_7_2 I J g = Xcb5_4_7_2 I J g := by
  decide +kernel

theorem hYtabb5_4_7_2 : ∀ I J g, Yb5_4_7_2 I J g = Ycb5_4_7_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb5_4_7_2 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T5_4_7
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_7 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xb5_4_7_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 hfuseZ_4_7 hfuseZ_5_3 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xcb5_4_7_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_4_7_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Yb5_4_7_2 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hfuseZ_5_4 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Ycb5_4_7_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_4_7_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 7) (realGauge.gaugeSizeL 5 4 7).1 (realGauge.gaugeSizeL 5 4 7).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb5_4_7_2 TL5_4_7 YLb5_4_7_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb5_4_7_3 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_7 (fuseRow (4 : ZMod 8) (7 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) ee) (fuseCol (4 : ZMod 8) (7 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 7) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb5_4_7_3 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((5 : ZMod 8) + 4) (7 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb5_4_7_3 : List (List (List ℤ)) :=
  [[[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb5_4_7_3 : List (List (List ℤ)) :=
  [[[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

noncomputable def Xcb5_4_7_3 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb5_4_7_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_4_7_3 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb5_4_7_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_4_7_3 : ∀ I J g, Xb5_4_7_3 I J g = Xcb5_4_7_3 I J g := by
  decide +kernel

theorem hYtabb5_4_7_3 : ∀ I J g, Yb5_4_7_3 I J g = Ycb5_4_7_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb5_4_7_3 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T5_4_7
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_7 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xb5_4_7_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 hfuseZ_4_7 hfuseZ_5_3 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xcb5_4_7_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_4_7_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Yb5_4_7_3 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hfuseZ_5_4 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Ycb5_4_7_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_4_7_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 7) (realGauge.gaugeSizeL 5 4 7).1 (realGauge.gaugeSizeL 5 4 7).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb5_4_7_3 TL5_4_7 YLb5_4_7_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc5_4_7_0 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_7 (fuseRow (4 : ZMod 8) (7 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) ee) (fuseCol (4 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 7) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc5_4_7_0 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) = (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (4 : ZMod 8)).1 (realSize (5 : ZMod 8) (4 : ZMod 8)).2 (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I)
          * realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_7 (fuseRow ((5 : ZMod 8) + 4) (7 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc5_4_7_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc5_4_7_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xcc5_4_7_0 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet XLc5_4_7_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_4_7_0 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet YLc5_4_7_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_4_7_0 : ∀ I J g, Xc5_4_7_0 I J g = Xcc5_4_7_0 I J g := by
  decide +kernel

theorem hYtabc5_4_7_0 : ∀ I J g, Yc5_4_7_0 I J g = Ycc5_4_7_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc5_4_7_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T5_4_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_7 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xc5_4_7_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 hfuseZ_4_7 hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xcc5_4_7_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_4_7_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Yc5_4_7_0 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Ycc5_4_7_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_4_7_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 7) (realGauge.gaugeSizeL 5 4 7).1 (realGauge.gaugeSizeL 5 4 7).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc5_4_7_0 TL5_4_7 YLc5_4_7_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc5_4_7_1 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_7 (fuseRow (4 : ZMod 8) (7 : ZMod 8) (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) (ro (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) ee) (fuseCol (4 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((4 : ZMod 8) + 7) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 I) (ri (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 J) g) (fuseCol (5 : ZMod 8) ((4 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc5_4_7_1 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) = (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (4 : ZMod 8)).1 (realSize (5 : ZMod 8) (4 : ZMod 8)).2 (lo (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I)
          * realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_7 (fuseRow ((5 : ZMod 8) + 4) (7 : ZMod 8) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) I) (li (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 4) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc5_4_7_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc5_4_7_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]]]

noncomputable def Xcc5_4_7_1 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet XLc5_4_7_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_4_7_1 : (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2) → Fin (realRepDim ((5 : ZMod 8) + 4 + 7).val) → ℤ :=
  fun r s g => coeffGet YLc5_4_7_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_4_7_1 : ∀ I J g, Xc5_4_7_1 I J g = Xcc5_4_7_1 I J g := by
  decide +kernel

theorem hYtabc5_4_7_1 : ∀ I J g, Yc5_4_7_1 I J g = Ycc5_4_7_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc5_4_7_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T5_4_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_4_7 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xc5_4_7_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 hfuseZ_4_7 hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Xcc5_4_7_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_4_7_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Yc5_4_7_1 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 4 + 7)) Ycc5_4_7_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 4 7).1 ⊕ Fin (realGauge.gaugeSizeL 5 4 7).2)) (realRepBasis ((5 : ZMod 8) + 4 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_4_7_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 4 + 7) (realGauge.gaugeSizeL 5 4 7).1 (realGauge.gaugeSizeL 5 4 7).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc5_4_7_1 TL5_4_7 YLc5_4_7_1 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint5_4_7 (i : Fin (realRepDim (5 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) i)) * T5_4_7
      = ((sgn (realRepBasisParity (5 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T5_4_7 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h0]; exact hinta5_4_7_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h1]; exact hinta5_4_7_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h2]; exact hinta5_4_7_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h3]; exact hinta5_4_7_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h4]; exact hinta5_4_7_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h5]; exact hinta5_4_7_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h6]; exact hinta5_4_7_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h7]; exact hinta5_4_7_7

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint5_4_7 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T5_4_7
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T5_4_7 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hintb5_4_7_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hintb5_4_7_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hintb5_4_7_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hintb5_4_7_3

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint5_4_7 (i : Fin (realRepDim (7 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) i)) * T5_4_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T5_4_7 * (realGauge.gaugeRouteL (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h0]; exact hintc5_4_7_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h1]; exact hintc5_4_7_1

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT5_4_7_mem_gInterSpace :
    gtOfT ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 T5_4_7 ∈ gInterSpace ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 hT5_4_7 hAint5_4_7 hBint5_4_7 hCint5_4_7

theorem gtOfT5_4_7_ne_zero : gtOfT ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 T5_4_7 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) hsz5_4_7 T5_4_7_ne_zero

theorem gInterSpace5_4_7_ne_bot : gInterSpace ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT5_4_7_mem_gInterSpace, gtOfT5_4_7_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_5_4_7 : gParity ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (5 : ZMod 8) (4 : ZMod 8) (7 : ZMod 8) gInterSpace5_4_7_ne_bot).symm

end Triple_5_4_7

/-! ### The triple `(5,5,0)`

`gaugeSizeL = gaugeSizeR = (2,2)`, `dim D_2 = 4`, certgen parity `0`; the unit-slot shortcut: the connector is the identity, so every certificate carries the sign `+1`. -/
section Triple_5_5_0
open Module
theorem hsz5_5_0 : realGauge.gaugeSizeR 5 5 0 = realGauge.gaugeSizeL 5 5 0 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`4 x 4 x 4`). -/
def TL5_5_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- The same literal read at the composite frame `Fin 2 ⊕ Fin 2`. -/
noncomputable def Tc5_5_0 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet TL5_5_0 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_2`. -/
noncomputable def T5_5_0 : ((realGauge.D ((5 : ZMod 8) + 5 + 0)).matrixSuper
    (realGauge.gaugeSizeL 5 5 0).1 (realGauge.gaugeSizeL 5 5 0).2).carrier :=
  matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Tc5_5_0

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT5_5_0 : T5_5_0 ∈ ((realGauge.D ((5 : ZMod 8) + 5 + 0)).matrixSuper
    (realGauge.gaugeSizeL 5 5 0).1 (realGauge.gaugeSizeL 5 5 0).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((5 : ZMod 8) + 5 + 0) Tc5_5_0 0 (by decide)

theorem T5_5_0_ne_zero : T5_5_0 ≠ 0 :=
  matOfCoeff_ne_zero ((5 : ZMod 8) + 5 + 0) Tc5_5_0 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa5_5_0_0 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) = (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (0 : ZMod 8)).1 (realSize (5 : ZMod 8) (0 : ZMod 8)).2 (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I)
          * realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((5 : ZMod 8) + 0) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) g) (fuseCol (5 : ZMod 8) ((5 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya5_5_0_0 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_2_0 (fuseRow ((5 : ZMod 8) + 5) (0 : ZMod 8) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 5) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa5_5_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa5_5_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xca5_5_0_0 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa5_5_0_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_5_0_0 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa5_5_0_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_5_0_0 : ∀ I J g, Xa5_5_0_0 I J g = Xca5_5_0_0 I J g := by
  decide +kernel

theorem hYtaba5_5_0_0 : ∀ I J g, Ya5_5_0_0 I J g = Yca5_5_0_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta5_5_0_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_5_0
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_5_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xa5_5_0_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 hfuseZ_5_5 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xca5_5_0_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_5_0_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Ya5_5_0_0 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hfuseZ_5_5 hfuseZ_2_0 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Yca5_5_0_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_5_0_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 5 + 0) (realGauge.gaugeSizeL 5 5 0).1 (realGauge.gaugeSizeL 5 5 0).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_5_0_0 TL5_5_0 YLa5_5_0_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa5_5_0_1 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) = (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (0 : ZMod 8)).1 (realSize (5 : ZMod 8) (0 : ZMod 8)).2 (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I)
          * realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((5 : ZMod 8) + 0) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) g) (fuseCol (5 : ZMod 8) ((5 : ZMod 8) + 0) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya5_5_0_1 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_2_0 (fuseRow ((5 : ZMod 8) + 5) (0 : ZMod 8) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 5) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa5_5_0_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa5_5_0_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca5_5_0_1 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa5_5_0_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_5_0_1 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa5_5_0_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_5_0_1 : ∀ I J g, Xa5_5_0_1 I J g = Xca5_5_0_1 I J g := by
  decide +kernel

theorem hYtaba5_5_0_1 : ∀ I J g, Ya5_5_0_1 I J g = Yca5_5_0_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta5_5_0_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_5_0
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_5_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xa5_5_0_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 hfuseZ_5_5 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xca5_5_0_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_5_0_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Ya5_5_0_1 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hfuseZ_5_5 hfuseZ_2_0 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Yca5_5_0_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_5_0_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 5 + 0) (realGauge.gaugeSizeL 5 5 0).1 (realGauge.gaugeSizeL 5 5 0).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_5_0_1 TL5_5_0 YLa5_5_0_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa5_5_0_2 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) = (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (0 : ZMod 8)).1 (realSize (5 : ZMod 8) (0 : ZMod 8)).2 (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I)
          * realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((5 : ZMod 8) + 0) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) g) (fuseCol (5 : ZMod 8) ((5 : ZMod 8) + 0) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya5_5_0_2 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_2_0 (fuseRow ((5 : ZMod 8) + 5) (0 : ZMod 8) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 5) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa5_5_0_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa5_5_0_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca5_5_0_2 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa5_5_0_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_5_0_2 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa5_5_0_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_5_0_2 : ∀ I J g, Xa5_5_0_2 I J g = Xca5_5_0_2 I J g := by
  decide +kernel

theorem hYtaba5_5_0_2 : ∀ I J g, Ya5_5_0_2 I J g = Yca5_5_0_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta5_5_0_2 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_5_0
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_5_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xa5_5_0_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 hfuseZ_5_5 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xca5_5_0_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_5_0_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Ya5_5_0_2 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hfuseZ_5_5 hfuseZ_2_0 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Yca5_5_0_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_5_0_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 5 + 0) (realGauge.gaugeSizeL 5 5 0).1 (realGauge.gaugeSizeL 5 5 0).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_5_0_2 TL5_5_0 YLa5_5_0_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa5_5_0_3 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) = (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (0 : ZMod 8)).1 (realSize (5 : ZMod 8) (0 : ZMod 8)).2 (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I)
          * realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((5 : ZMod 8) + 0) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) g) (fuseCol (5 : ZMod 8) ((5 : ZMod 8) + 0) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya5_5_0_3 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_2_0 (fuseRow ((5 : ZMod 8) + 5) (0 : ZMod 8) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 5) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa5_5_0_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa5_5_0_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]]]

noncomputable def Xca5_5_0_3 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa5_5_0_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_5_0_3 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa5_5_0_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_5_0_3 : ∀ I J g, Xa5_5_0_3 I J g = Xca5_5_0_3 I J g := by
  decide +kernel

theorem hYtaba5_5_0_3 : ∀ I J g, Ya5_5_0_3 I J g = Yca5_5_0_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta5_5_0_3 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_5_0
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_5_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xa5_5_0_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 hfuseZ_5_5 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xca5_5_0_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_5_0_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Ya5_5_0_3 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hfuseZ_5_5 hfuseZ_2_0 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Yca5_5_0_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_5_0_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 5 + 0) (realGauge.gaugeSizeL 5 5 0).1 (realGauge.gaugeSizeL 5 5 0).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_5_0_3 TL5_5_0 YLa5_5_0_3 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Xa5_5_0_4 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) = (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (0 : ZMod 8)).1 (realSize (5 : ZMod 8) (0 : ZMod 8)).2 (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I)
          * realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((5 : ZMod 8) + 0) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) g) (fuseCol (5 : ZMod 8) ((5 : ZMod 8) + 0) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Ya5_5_0_4 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_2_0 (fuseRow ((5 : ZMod 8) + 5) (0 : ZMod 8) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 5) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `4`, pre-tabulated. -/
def XLa5_5_0_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `4`, pre-tabulated. -/
def YLa5_5_0_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]]]

noncomputable def Xca5_5_0_4 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa5_5_0_4 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_5_0_4 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa5_5_0_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_5_0_4 : ∀ I J g, Xa5_5_0_4 I J g = Xca5_5_0_4 I J g := by
  decide +kernel

theorem hYtaba5_5_0_4 : ∀ I J g, Ya5_5_0_4 I J g = Yca5_5_0_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `4`** (Koszul sign `+1`). -/
theorem hinta5_5_0_4 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_5_0
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_5_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xa5_5_0_4 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 hfuseZ_5_5 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xca5_5_0_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_5_0_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Ya5_5_0_4 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hfuseZ_5_5 hfuseZ_2_0 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Yca5_5_0_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_5_0_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 5 + 0) (realGauge.gaugeSizeL 5 5 0).1 (realGauge.gaugeSizeL 5 5 0).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_5_0_4 TL5_5_0 YLa5_5_0_4 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Xa5_5_0_5 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) = (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (0 : ZMod 8)).1 (realSize (5 : ZMod 8) (0 : ZMod 8)).2 (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I)
          * realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((5 : ZMod 8) + 0) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) g) (fuseCol (5 : ZMod 8) ((5 : ZMod 8) + 0) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Ya5_5_0_5 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_2_0 (fuseRow ((5 : ZMod 8) + 5) (0 : ZMod 8) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 5) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `5`, pre-tabulated. -/
def XLa5_5_0_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `5`, pre-tabulated. -/
def YLa5_5_0_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca5_5_0_5 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa5_5_0_5 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_5_0_5 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa5_5_0_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_5_0_5 : ∀ I J g, Xa5_5_0_5 I J g = Xca5_5_0_5 I J g := by
  decide +kernel

theorem hYtaba5_5_0_5 : ∀ I J g, Ya5_5_0_5 I J g = Yca5_5_0_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `5`** (Koszul sign `+1`). -/
theorem hinta5_5_0_5 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_5_0
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_5_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xa5_5_0_5 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 hfuseZ_5_5 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xca5_5_0_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_5_0_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Ya5_5_0_5 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hfuseZ_5_5 hfuseZ_2_0 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Yca5_5_0_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_5_0_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 5 + 0) (realGauge.gaugeSizeL 5 5 0).1 (realGauge.gaugeSizeL 5 5 0).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_5_0_5 TL5_5_0 YLa5_5_0_5 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Xa5_5_0_6 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) = (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (0 : ZMod 8)).1 (realSize (5 : ZMod 8) (0 : ZMod 8)).2 (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I)
          * realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((5 : ZMod 8) + 0) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) g) (fuseCol (5 : ZMod 8) ((5 : ZMod 8) + 0) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Ya5_5_0_6 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_2_0 (fuseRow ((5 : ZMod 8) + 5) (0 : ZMod 8) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 5) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `6`, pre-tabulated. -/
def XLa5_5_0_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `6`, pre-tabulated. -/
def YLa5_5_0_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca5_5_0_6 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa5_5_0_6 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_5_0_6 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa5_5_0_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_5_0_6 : ∀ I J g, Xa5_5_0_6 I J g = Xca5_5_0_6 I J g := by
  decide +kernel

theorem hYtaba5_5_0_6 : ∀ I J g, Ya5_5_0_6 I J g = Yca5_5_0_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `6`** (Koszul sign `+1`). -/
theorem hinta5_5_0_6 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_5_0
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_5_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xa5_5_0_6 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 hfuseZ_5_5 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xca5_5_0_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_5_0_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Ya5_5_0_6 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hfuseZ_5_5 hfuseZ_2_0 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Yca5_5_0_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_5_0_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 5 + 0) (realGauge.gaugeSizeL 5 5 0).1 (realGauge.gaugeSizeL 5 5 0).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_5_0_6 TL5_5_0 YLa5_5_0_6 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Xa5_5_0_7 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) = (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (0 : ZMod 8)).1 (realSize (5 : ZMod 8) (0 : ZMod 8)).2 (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I)
          * realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((5 : ZMod 8) + 0) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) g) (fuseCol (5 : ZMod 8) ((5 : ZMod 8) + 0) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Ya5_5_0_7 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_2_0 (fuseRow ((5 : ZMod 8) + 5) (0 : ZMod 8) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 5) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `7`, pre-tabulated. -/
def XLa5_5_0_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `7`, pre-tabulated. -/
def YLa5_5_0_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca5_5_0_7 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa5_5_0_7 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_5_0_7 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa5_5_0_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_5_0_7 : ∀ I J g, Xa5_5_0_7 I J g = Xca5_5_0_7 I J g := by
  decide +kernel

theorem hYtaba5_5_0_7 : ∀ I J g, Ya5_5_0_7 I J g = Yca5_5_0_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `7`** (Koszul sign `+1`). -/
theorem hinta5_5_0_7 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_5_0
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_5_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xa5_5_0_7 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 hfuseZ_5_5 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xca5_5_0_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_5_0_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Ya5_5_0_7 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hfuseZ_5_5 hfuseZ_2_0 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Yca5_5_0_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_5_0_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 5 + 0) (realGauge.gaugeSizeL 5 5 0).1 (realGauge.gaugeSizeL 5 5 0).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_5_0_7 TL5_5_0 YLa5_5_0_7 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb5_5_0_0 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_0 (fuseRow (5 : ZMod 8) (0 : ZMod 8) (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) ee) (fuseCol (5 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((5 : ZMod 8) + 0) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) g) (fuseCol (5 : ZMod 8) ((5 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb5_5_0_0 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_2_0 (fuseRow ((5 : ZMod 8) + 5) (0 : ZMod 8) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 5) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb5_5_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb5_5_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcb5_5_0_0 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb5_5_0_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_5_0_0 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb5_5_0_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_5_0_0 : ∀ I J g, Xb5_5_0_0 I J g = Xcb5_5_0_0 I J g := by
  decide +kernel

theorem hYtabb5_5_0_0 : ∀ I J g, Yb5_5_0_0 I J g = Ycb5_5_0_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb5_5_0_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_5_0
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_5_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xb5_5_0_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 hfuseZ_5_0 hfuseZ_5_5 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xcb5_5_0_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_5_0_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Yb5_5_0_0 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hfuseZ_5_5 hfuseZ_2_0 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Ycb5_5_0_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_5_0_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 5 + 0) (realGauge.gaugeSizeL 5 5 0).1 (realGauge.gaugeSizeL 5 5 0).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb5_5_0_0 TL5_5_0 YLb5_5_0_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb5_5_0_1 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_0 (fuseRow (5 : ZMod 8) (0 : ZMod 8) (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) ee) (fuseCol (5 : ZMod 8) (0 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((5 : ZMod 8) + 0) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) g) (fuseCol (5 : ZMod 8) ((5 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb5_5_0_1 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_2_0 (fuseRow ((5 : ZMod 8) + 5) (0 : ZMod 8) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 5) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb5_5_0_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb5_5_0_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb5_5_0_1 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb5_5_0_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_5_0_1 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb5_5_0_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_5_0_1 : ∀ I J g, Xb5_5_0_1 I J g = Xcb5_5_0_1 I J g := by
  decide +kernel

theorem hYtabb5_5_0_1 : ∀ I J g, Yb5_5_0_1 I J g = Ycb5_5_0_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb5_5_0_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_5_0
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_5_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xb5_5_0_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 hfuseZ_5_0 hfuseZ_5_5 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xcb5_5_0_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_5_0_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Yb5_5_0_1 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hfuseZ_5_5 hfuseZ_2_0 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Ycb5_5_0_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_5_0_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 5 + 0) (realGauge.gaugeSizeL 5 5 0).1 (realGauge.gaugeSizeL 5 5 0).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb5_5_0_1 TL5_5_0 YLb5_5_0_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb5_5_0_2 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_0 (fuseRow (5 : ZMod 8) (0 : ZMod 8) (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) ee) (fuseCol (5 : ZMod 8) (0 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((5 : ZMod 8) + 0) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) g) (fuseCol (5 : ZMod 8) ((5 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb5_5_0_2 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_2_0 (fuseRow ((5 : ZMod 8) + 5) (0 : ZMod 8) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 5) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb5_5_0_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb5_5_0_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb5_5_0_2 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb5_5_0_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_5_0_2 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb5_5_0_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_5_0_2 : ∀ I J g, Xb5_5_0_2 I J g = Xcb5_5_0_2 I J g := by
  decide +kernel

theorem hYtabb5_5_0_2 : ∀ I J g, Yb5_5_0_2 I J g = Ycb5_5_0_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb5_5_0_2 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_5_0
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_5_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xb5_5_0_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 hfuseZ_5_0 hfuseZ_5_5 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xcb5_5_0_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_5_0_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Yb5_5_0_2 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hfuseZ_5_5 hfuseZ_2_0 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Ycb5_5_0_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_5_0_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 5 + 0) (realGauge.gaugeSizeL 5 5 0).1 (realGauge.gaugeSizeL 5 5 0).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb5_5_0_2 TL5_5_0 YLb5_5_0_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb5_5_0_3 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_0 (fuseRow (5 : ZMod 8) (0 : ZMod 8) (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) ee) (fuseCol (5 : ZMod 8) (0 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((5 : ZMod 8) + 0) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) g) (fuseCol (5 : ZMod 8) ((5 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb5_5_0_3 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_2_0 (fuseRow ((5 : ZMod 8) + 5) (0 : ZMod 8) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 5) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb5_5_0_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb5_5_0_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb5_5_0_3 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb5_5_0_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_5_0_3 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb5_5_0_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_5_0_3 : ∀ I J g, Xb5_5_0_3 I J g = Xcb5_5_0_3 I J g := by
  decide +kernel

theorem hYtabb5_5_0_3 : ∀ I J g, Yb5_5_0_3 I J g = Ycb5_5_0_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb5_5_0_3 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_5_0
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_5_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xb5_5_0_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 hfuseZ_5_0 hfuseZ_5_5 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xcb5_5_0_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_5_0_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Yb5_5_0_3 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hfuseZ_5_5 hfuseZ_2_0 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Ycb5_5_0_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_5_0_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 5 + 0) (realGauge.gaugeSizeL 5 5 0).1 (realGauge.gaugeSizeL 5 5 0).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb5_5_0_3 TL5_5_0 YLb5_5_0_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Xb5_5_0_4 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_0 (fuseRow (5 : ZMod 8) (0 : ZMod 8) (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) ee) (fuseCol (5 : ZMod 8) (0 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((5 : ZMod 8) + 0) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) g) (fuseCol (5 : ZMod 8) ((5 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Yb5_5_0_4 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_2_0 (fuseRow ((5 : ZMod 8) + 5) (0 : ZMod 8) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 5) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `4`, pre-tabulated. -/
def XLb5_5_0_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `4`, pre-tabulated. -/
def YLb5_5_0_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb5_5_0_4 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb5_5_0_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_5_0_4 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb5_5_0_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_5_0_4 : ∀ I J g, Xb5_5_0_4 I J g = Xcb5_5_0_4 I J g := by
  decide +kernel

theorem hYtabb5_5_0_4 : ∀ I J g, Yb5_5_0_4 I J g = Ycb5_5_0_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `4`** (Koszul sign `+1`). -/
theorem hintb5_5_0_4 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_5_0
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_5_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xb5_5_0_4 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 hfuseZ_5_0 hfuseZ_5_5 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xcb5_5_0_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_5_0_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Yb5_5_0_4 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hfuseZ_5_5 hfuseZ_2_0 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Ycb5_5_0_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_5_0_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 5 + 0) (realGauge.gaugeSizeL 5 5 0).1 (realGauge.gaugeSizeL 5 5 0).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb5_5_0_4 TL5_5_0 YLb5_5_0_4 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Xb5_5_0_5 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_0 (fuseRow (5 : ZMod 8) (0 : ZMod 8) (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) ee) (fuseCol (5 : ZMod 8) (0 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((5 : ZMod 8) + 0) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) g) (fuseCol (5 : ZMod 8) ((5 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Yb5_5_0_5 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_2_0 (fuseRow ((5 : ZMod 8) + 5) (0 : ZMod 8) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 5) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `5`, pre-tabulated. -/
def XLb5_5_0_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `5`, pre-tabulated. -/
def YLb5_5_0_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb5_5_0_5 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb5_5_0_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_5_0_5 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb5_5_0_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_5_0_5 : ∀ I J g, Xb5_5_0_5 I J g = Xcb5_5_0_5 I J g := by
  decide +kernel

theorem hYtabb5_5_0_5 : ∀ I J g, Yb5_5_0_5 I J g = Ycb5_5_0_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintb5_5_0_5 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_5_0
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_5_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xb5_5_0_5 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 hfuseZ_5_0 hfuseZ_5_5 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xcb5_5_0_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_5_0_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Yb5_5_0_5 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hfuseZ_5_5 hfuseZ_2_0 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Ycb5_5_0_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_5_0_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 5 + 0) (realGauge.gaugeSizeL 5 5 0).1 (realGauge.gaugeSizeL 5 5 0).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb5_5_0_5 TL5_5_0 YLb5_5_0_5 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Xb5_5_0_6 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_0 (fuseRow (5 : ZMod 8) (0 : ZMod 8) (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) ee) (fuseCol (5 : ZMod 8) (0 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((5 : ZMod 8) + 0) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) g) (fuseCol (5 : ZMod 8) ((5 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Yb5_5_0_6 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_2_0 (fuseRow ((5 : ZMod 8) + 5) (0 : ZMod 8) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 5) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `6`, pre-tabulated. -/
def XLb5_5_0_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]]]

/-- Left route at the `b`-slot generator `6`, pre-tabulated. -/
def YLb5_5_0_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]]]

noncomputable def Xcb5_5_0_6 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb5_5_0_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_5_0_6 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb5_5_0_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_5_0_6 : ∀ I J g, Xb5_5_0_6 I J g = Xcb5_5_0_6 I J g := by
  decide +kernel

theorem hYtabb5_5_0_6 : ∀ I J g, Yb5_5_0_6 I J g = Ycb5_5_0_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintb5_5_0_6 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_5_0
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_5_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xb5_5_0_6 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 hfuseZ_5_0 hfuseZ_5_5 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xcb5_5_0_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_5_0_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Yb5_5_0_6 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hfuseZ_5_5 hfuseZ_2_0 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Ycb5_5_0_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_5_0_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 5 + 0) (realGauge.gaugeSizeL 5 5 0).1 (realGauge.gaugeSizeL 5 5 0).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb5_5_0_6 TL5_5_0 YLb5_5_0_6 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Xb5_5_0_7 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_0 (fuseRow (5 : ZMod 8) (0 : ZMod 8) (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) ee) (fuseCol (5 : ZMod 8) (0 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((5 : ZMod 8) + 0) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) g) (fuseCol (5 : ZMod 8) ((5 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Yb5_5_0_7 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_5 (fuseRow (5 : ZMod 8) (5 : ZMod 8) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_2_0 (fuseRow ((5 : ZMod 8) + 5) (0 : ZMod 8) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 5) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `7`, pre-tabulated. -/
def XLb5_5_0_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `7`, pre-tabulated. -/
def YLb5_5_0_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0]]]

noncomputable def Xcb5_5_0_7 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb5_5_0_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_5_0_7 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb5_5_0_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_5_0_7 : ∀ I J g, Xb5_5_0_7 I J g = Xcb5_5_0_7 I J g := by
  decide +kernel

theorem hYtabb5_5_0_7 : ∀ I J g, Yb5_5_0_7 I J g = Ycb5_5_0_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `7`** (Koszul sign `+1`). -/
theorem hintb5_5_0_7 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_5_0
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_5_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xb5_5_0_7 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 hfuseZ_5_0 hfuseZ_5_5 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xcb5_5_0_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_5_0_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Yb5_5_0_7 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hfuseZ_5_5 hfuseZ_2_0 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Ycb5_5_0_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_5_0_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 5 + 0) (realGauge.gaugeSizeL 5 5 0).1 (realGauge.gaugeSizeL 5 5 0).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb5_5_0_7 TL5_5_0 YLb5_5_0_7 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc5_5_0_0 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_0 (fuseRow (5 : ZMod 8) (0 : ZMod 8) (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) (ro (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) ee) (fuseCol (5 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_5_5 (fuseRow (5 : ZMod 8) ((5 : ZMod 8) + 0) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 I) (ri (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 J) g) (fuseCol (5 : ZMod 8) ((5 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc5_5_0_0 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) = (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (5 : ZMod 8)).1 (realSize (5 : ZMod 8) (5 : ZMod 8)).2 (lo (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I)
          * realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_0 (fuseRow ((5 : ZMod 8) + 5) (0 : ZMod 8) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 5) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc5_5_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc5_5_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcc5_5_0_0 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet XLc5_5_0_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_5_0_0 : (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2) → Fin (realRepDim ((5 : ZMod 8) + 5 + 0).val) → ℤ :=
  fun r s g => coeffGet YLc5_5_0_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_5_0_0 : ∀ I J g, Xc5_5_0_0 I J g = Xcc5_5_0_0 I J g := by
  decide +kernel

theorem hYtabc5_5_0_0 : ∀ I J g, Yc5_5_0_0 I J g = Ycc5_5_0_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc5_5_0_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))) * T5_5_0
      = ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_5_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xc5_5_0_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 hfuseZ_5_0 hfuseZ_5_5 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Xcc5_5_0_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_5_0_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Yc5_5_0_0 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hfuseZ_2_0 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 5 + 0)) Ycc5_5_0_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 5 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 5 0).2)) (realRepBasis ((5 : ZMod 8) + 5 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_5_0_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 5 + 0) (realGauge.gaugeSizeL 5 5 0).1 (realGauge.gaugeSizeL 5 5 0).2 ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc5_5_0_0 TL5_5_0 YLc5_5_0_0 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint5_5_0 (i : Fin (realRepDim (5 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) i)) * T5_5_0
      = ((sgn (realRepBasisParity (5 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T5_5_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h0]; exact hinta5_5_0_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h1]; exact hinta5_5_0_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h2]; exact hinta5_5_0_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h3]; exact hinta5_5_0_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h4]; exact hinta5_5_0_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h5]; exact hinta5_5_0_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h6]; exact hinta5_5_0_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h7]; exact hinta5_5_0_7

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint5_5_0 (i : Fin (realRepDim (5 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) i)) * T5_5_0
      = ((sgn (realRepBasisParity (5 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T5_5_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h0]; exact hintb5_5_0_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h1]; exact hintb5_5_0_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h2]; exact hintb5_5_0_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h3]; exact hintb5_5_0_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h4]; exact hintb5_5_0_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h5]; exact hintb5_5_0_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h6]; exact hintb5_5_0_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h7]; exact hintb5_5_0_7

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint5_5_0 (i : Fin (realRepDim (0 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) i)) * T5_5_0
      = ((sgn (realRepBasisParity (0 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T5_5_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 1 := i.isLt
  have h0 : (i : ℕ) = 0 := by omega
  rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) from Fin.ext h0]
  exact hintc5_5_0_0

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT5_5_0_mem_gInterSpace :
    gtOfT ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 T5_5_0 ∈ gInterSpace ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 hT5_5_0 hAint5_5_0 hBint5_5_0 hCint5_5_0

theorem gtOfT5_5_0_ne_zero : gtOfT ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 T5_5_0 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) hsz5_5_0 T5_5_0_ne_zero

theorem gInterSpace5_5_0_ne_bot : gInterSpace ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT5_5_0_mem_gInterSpace, gtOfT5_5_0_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_5_5_0 : gParity ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (5 : ZMod 8) (5 : ZMod 8) (0 : ZMod 8) gInterSpace5_5_0_ne_bot).symm

end Triple_5_5_0

end G5_18
end TripleCerts
end GaugeChi
end Superfusion

/-! ### Kernel self-check -/

#print axioms Superfusion.GaugeChi.TripleCerts.G5_18.gParity_5_4_1
#print axioms Superfusion.GaugeChi.TripleCerts.G5_18.gParity_5_4_2
#print axioms Superfusion.GaugeChi.TripleCerts.G5_18.gParity_5_4_6
#print axioms Superfusion.GaugeChi.TripleCerts.G5_18.gParity_5_4_7
#print axioms Superfusion.GaugeChi.TripleCerts.G5_18.gParity_5_5_0
