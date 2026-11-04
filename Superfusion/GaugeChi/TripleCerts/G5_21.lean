/-
Superfusion / GaugeChi / TripleCerts / G5_21

**GENERATED FILE — do not edit.**  Regenerate with

    python3 scripts/certgen/gen_triple_certs.py \
        --triples 5,7,0 5,7,1 5,7,2 5,7,3 5,7,4 5,7,5 \
        --module G5_21 \
        --out Superfusion/GaugeChi/TripleCerts/G5_21.lean

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

Triples (6): (5,7,0), (5,7,1), (5,7,2), (5,7,3), (5,7,4), (5,7,5).
Unit-slot triples (`a = 0` or `b = 0` or `c = 0`) in this batch: (5,7,0).
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
namespace G5_21

open Module

/-! ### The fusion shadows this batch uses (18 of the 64)

They are declared at the enclosing `TripleCerts` namespace by
`TripleCerts/FuseShadows.lean`, so the short names below resolve
unqualified and no `open` is needed:

  `fuseZ_4_0`, `fuseZ_4_1`, `fuseZ_4_2`, `fuseZ_4_3`, `fuseZ_4_4`, `fuseZ_4_5`, `fuseZ_5_0`, `fuseZ_5_1`, `fuseZ_5_2`, `fuseZ_5_3`, `fuseZ_5_4`, `fuseZ_5_7`, `fuseZ_7_0`, `fuseZ_7_1`, `fuseZ_7_2`, `fuseZ_7_3`, `fuseZ_7_4`, `fuseZ_7_5`. -/

/-! ### The triple `(5,7,0)`

`gaugeSizeL = gaugeSizeR = (1,1)`, `dim D_4 = 4`, certgen parity `0`; the unit-slot shortcut: the connector is the identity, so every certificate carries the sign `+1`. -/
section Triple_5_7_0
open Module
theorem hsz5_7_0 : realGauge.gaugeSizeR 5 7 0 = realGauge.gaugeSizeL 5 7 0 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`2 x 2 x 4`). -/
def TL5_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0]]]

/-- The same literal read at the composite frame `Fin 1 ⊕ Fin 1`. -/
noncomputable def Tc5_7_0 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun r s g => coeffGet TL5_7_0 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_4`. -/
noncomputable def T5_7_0 : ((realGauge.D ((5 : ZMod 8) + 7 + 0)).matrixSuper
    (realGauge.gaugeSizeL 5 7 0).1 (realGauge.gaugeSizeL 5 7 0).2).carrier :=
  matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Tc5_7_0

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT5_7_0 : T5_7_0 ∈ ((realGauge.D ((5 : ZMod 8) + 7 + 0)).matrixSuper
    (realGauge.gaugeSizeL 5 7 0).1 (realGauge.gaugeSizeL 5 7 0).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((5 : ZMod 8) + 7 + 0) Tc5_7_0 0 (by decide)

theorem T5_7_0_ne_zero : T5_7_0 ≠ 0 :=
  matOfCoeff_ne_zero ((5 : ZMod 8) + 7 + 0) Tc5_7_0 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa5_7_0_0 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (0 : ZMod 8)).1 (realSize (7 : ZMod 8) (0 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I)
          * realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_7 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 0) (ri (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I) (ri (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya5_7_0_0 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_0 (fuseRow ((5 : ZMod 8) + 7) (0 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa5_7_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa5_7_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xca5_7_0_0 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_0_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_0_0 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_0_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_0_0 : ∀ I J g, Xa5_7_0_0 I J g = Xca5_7_0_0 I J g := by
  decide +kernel

theorem hYtaba5_7_0_0 : ∀ I J g, Ya5_7_0_0 I J g = Yca5_7_0_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta5_7_0_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_0
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_7_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Xa5_7_0_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 hfuseZ_5_7 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Xca5_7_0_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2)) (realRepBasis ((5 : ZMod 8) + 7 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_0_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Ya5_7_0_0 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hfuseZ_5_7 hfuseZ_4_0 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Yca5_7_0_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2)) (realRepBasis ((5 : ZMod 8) + 7 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_0_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 0) (realGauge.gaugeSizeL 5 7 0).1 (realGauge.gaugeSizeL 5 7 0).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_7_0_0 TL5_7_0 YLa5_7_0_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa5_7_0_1 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (0 : ZMod 8)).1 (realSize (7 : ZMod 8) (0 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I)
          * realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_7 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 0) (ri (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I) (ri (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 0) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya5_7_0_1 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_0 (fuseRow ((5 : ZMod 8) + 7) (0 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa5_7_0_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [1, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa5_7_0_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [1, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca5_7_0_1 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_0_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_0_1 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_0_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_0_1 : ∀ I J g, Xa5_7_0_1 I J g = Xca5_7_0_1 I J g := by
  decide +kernel

theorem hYtaba5_7_0_1 : ∀ I J g, Ya5_7_0_1 I J g = Yca5_7_0_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta5_7_0_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_0
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_7_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Xa5_7_0_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 hfuseZ_5_7 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Xca5_7_0_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2)) (realRepBasis ((5 : ZMod 8) + 7 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_0_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Ya5_7_0_1 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hfuseZ_5_7 hfuseZ_4_0 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Yca5_7_0_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2)) (realRepBasis ((5 : ZMod 8) + 7 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_0_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 0) (realGauge.gaugeSizeL 5 7 0).1 (realGauge.gaugeSizeL 5 7 0).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_7_0_1 TL5_7_0 YLa5_7_0_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa5_7_0_2 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (0 : ZMod 8)).1 (realSize (7 : ZMod 8) (0 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I)
          * realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_7 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 0) (ri (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I) (ri (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 0) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya5_7_0_2 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_0 (fuseRow ((5 : ZMod 8) + 7) (0 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa5_7_0_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, -1, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa5_7_0_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, -1, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca5_7_0_2 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_0_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_0_2 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_0_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_0_2 : ∀ I J g, Xa5_7_0_2 I J g = Xca5_7_0_2 I J g := by
  decide +kernel

theorem hYtaba5_7_0_2 : ∀ I J g, Ya5_7_0_2 I J g = Yca5_7_0_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta5_7_0_2 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_0
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_7_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Xa5_7_0_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 hfuseZ_5_7 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Xca5_7_0_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2)) (realRepBasis ((5 : ZMod 8) + 7 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_0_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Ya5_7_0_2 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hfuseZ_5_7 hfuseZ_4_0 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Yca5_7_0_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2)) (realRepBasis ((5 : ZMod 8) + 7 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_0_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 0) (realGauge.gaugeSizeL 5 7 0).1 (realGauge.gaugeSizeL 5 7 0).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_7_0_2 TL5_7_0 YLa5_7_0_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa5_7_0_3 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (0 : ZMod 8)).1 (realSize (7 : ZMod 8) (0 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I)
          * realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_7 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 0) (ri (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I) (ri (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 0) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya5_7_0_3 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_0 (fuseRow ((5 : ZMod 8) + 7) (0 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa5_7_0_3 : List (List (List ℤ)) :=
  [[[0, -1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa5_7_0_3 : List (List (List ℤ)) :=
  [[[0, -1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0]]]

noncomputable def Xca5_7_0_3 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_0_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_0_3 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_0_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_0_3 : ∀ I J g, Xa5_7_0_3 I J g = Xca5_7_0_3 I J g := by
  decide +kernel

theorem hYtaba5_7_0_3 : ∀ I J g, Ya5_7_0_3 I J g = Yca5_7_0_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta5_7_0_3 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_0
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_7_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Xa5_7_0_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 hfuseZ_5_7 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Xca5_7_0_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2)) (realRepBasis ((5 : ZMod 8) + 7 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_0_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Ya5_7_0_3 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hfuseZ_5_7 hfuseZ_4_0 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Yca5_7_0_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2)) (realRepBasis ((5 : ZMod 8) + 7 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_0_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 0) (realGauge.gaugeSizeL 5 7 0).1 (realGauge.gaugeSizeL 5 7 0).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_7_0_3 TL5_7_0 YLa5_7_0_3 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Xa5_7_0_4 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (0 : ZMod 8)).1 (realSize (7 : ZMod 8) (0 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I)
          * realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_7 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 0) (ri (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I) (ri (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 0) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Ya5_7_0_4 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_0 (fuseRow ((5 : ZMod 8) + 7) (0 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `4`, pre-tabulated. -/
def XLa5_7_0_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `4`, pre-tabulated. -/
def YLa5_7_0_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0]]]

noncomputable def Xca5_7_0_4 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_0_4 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_0_4 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_0_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_0_4 : ∀ I J g, Xa5_7_0_4 I J g = Xca5_7_0_4 I J g := by
  decide +kernel

theorem hYtaba5_7_0_4 : ∀ I J g, Ya5_7_0_4 I J g = Yca5_7_0_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `4`** (Koszul sign `+1`). -/
theorem hinta5_7_0_4 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_0
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_7_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Xa5_7_0_4 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 hfuseZ_5_7 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Xca5_7_0_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2)) (realRepBasis ((5 : ZMod 8) + 7 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_0_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Ya5_7_0_4 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hfuseZ_5_7 hfuseZ_4_0 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Yca5_7_0_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2)) (realRepBasis ((5 : ZMod 8) + 7 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_0_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 0) (realGauge.gaugeSizeL 5 7 0).1 (realGauge.gaugeSizeL 5 7 0).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_7_0_4 TL5_7_0 YLa5_7_0_4 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Xa5_7_0_5 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (0 : ZMod 8)).1 (realSize (7 : ZMod 8) (0 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I)
          * realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_7 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 0) (ri (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I) (ri (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 0) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Ya5_7_0_5 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_0 (fuseRow ((5 : ZMod 8) + 7) (0 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `5`, pre-tabulated. -/
def XLa5_7_0_5 : List (List (List ℤ)) :=
  [[[0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 1, 0]]]

/-- Left route at the `a`-slot generator `5`, pre-tabulated. -/
def YLa5_7_0_5 : List (List (List ℤ)) :=
  [[[0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 1, 0]]]

noncomputable def Xca5_7_0_5 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_0_5 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_0_5 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_0_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_0_5 : ∀ I J g, Xa5_7_0_5 I J g = Xca5_7_0_5 I J g := by
  decide +kernel

theorem hYtaba5_7_0_5 : ∀ I J g, Ya5_7_0_5 I J g = Yca5_7_0_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `5`** (Koszul sign `+1`). -/
theorem hinta5_7_0_5 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_0
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_7_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Xa5_7_0_5 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 hfuseZ_5_7 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Xca5_7_0_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2)) (realRepBasis ((5 : ZMod 8) + 7 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_0_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Ya5_7_0_5 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hfuseZ_5_7 hfuseZ_4_0 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Yca5_7_0_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2)) (realRepBasis ((5 : ZMod 8) + 7 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_0_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 0) (realGauge.gaugeSizeL 5 7 0).1 (realGauge.gaugeSizeL 5 7 0).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_7_0_5 TL5_7_0 YLa5_7_0_5 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Xa5_7_0_6 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (0 : ZMod 8)).1 (realSize (7 : ZMod 8) (0 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I)
          * realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_7 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 0) (ri (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I) (ri (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 0) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Ya5_7_0_6 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_0 (fuseRow ((5 : ZMod 8) + 7) (0 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `6`, pre-tabulated. -/
def XLa5_7_0_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1]]]

/-- Left route at the `a`-slot generator `6`, pre-tabulated. -/
def YLa5_7_0_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1]]]

noncomputable def Xca5_7_0_6 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_0_6 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_0_6 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_0_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_0_6 : ∀ I J g, Xa5_7_0_6 I J g = Xca5_7_0_6 I J g := by
  decide +kernel

theorem hYtaba5_7_0_6 : ∀ I J g, Ya5_7_0_6 I J g = Yca5_7_0_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `6`** (Koszul sign `+1`). -/
theorem hinta5_7_0_6 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_0
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_7_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Xa5_7_0_6 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 hfuseZ_5_7 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Xca5_7_0_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2)) (realRepBasis ((5 : ZMod 8) + 7 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_0_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Ya5_7_0_6 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hfuseZ_5_7 hfuseZ_4_0 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Yca5_7_0_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2)) (realRepBasis ((5 : ZMod 8) + 7 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_0_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 0) (realGauge.gaugeSizeL 5 7 0).1 (realGauge.gaugeSizeL 5 7 0).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_7_0_6 TL5_7_0 YLa5_7_0_6 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Xa5_7_0_7 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (0 : ZMod 8)).1 (realSize (7 : ZMod 8) (0 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I)
          * realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_7 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 0) (ri (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I) (ri (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 0) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Ya5_7_0_7 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_0 (fuseRow ((5 : ZMod 8) + 7) (0 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `7`, pre-tabulated. -/
def XLa5_7_0_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, -1]],
   [[0, 0, 0, -1], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `7`, pre-tabulated. -/
def YLa5_7_0_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, -1]],
   [[0, 0, 0, -1], [0, 0, 0, 0]]]

noncomputable def Xca5_7_0_7 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_0_7 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_0_7 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_0_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_0_7 : ∀ I J g, Xa5_7_0_7 I J g = Xca5_7_0_7 I J g := by
  decide +kernel

theorem hYtaba5_7_0_7 : ∀ I J g, Ya5_7_0_7 I J g = Yca5_7_0_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `7`** (Koszul sign `+1`). -/
theorem hinta5_7_0_7 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_0
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_7_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Xa5_7_0_7 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 hfuseZ_5_7 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Xca5_7_0_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2)) (realRepBasis ((5 : ZMod 8) + 7 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_0_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Ya5_7_0_7 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hfuseZ_5_7 hfuseZ_4_0 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Yca5_7_0_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2)) (realRepBasis ((5 : ZMod 8) + 7 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_0_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 0) (realGauge.gaugeSizeL 5 7 0).1 (realGauge.gaugeSizeL 5 7 0).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_7_0_7 TL5_7_0 YLa5_7_0_7 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb5_7_0_0 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_0 (fuseRow (7 : ZMod 8) (0 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I) (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 J) ee) (fuseCol (7 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_5_7 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 0) (ri (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I) (ri (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb5_7_0_0 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_0 (fuseRow ((5 : ZMod 8) + 7) (0 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb5_7_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb5_7_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcb5_7_0_0 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb5_7_0_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_7_0_0 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb5_7_0_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_7_0_0 : ∀ I J g, Xb5_7_0_0 I J g = Xcb5_7_0_0 I J g := by
  decide +kernel

theorem hYtabb5_7_0_0 : ∀ I J g, Yb5_7_0_0 I J g = Ycb5_7_0_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb5_7_0_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T5_7_0
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_7_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Xb5_7_0_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 hfuseZ_7_0 hfuseZ_5_7 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Xcb5_7_0_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2)) (realRepBasis ((5 : ZMod 8) + 7 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_7_0_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Yb5_7_0_0 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hfuseZ_5_7 hfuseZ_4_0 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Ycb5_7_0_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2)) (realRepBasis ((5 : ZMod 8) + 7 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_7_0_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 0) (realGauge.gaugeSizeL 5 7 0).1 (realGauge.gaugeSizeL 5 7 0).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb5_7_0_0 TL5_7_0 YLb5_7_0_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb5_7_0_1 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_0 (fuseRow (7 : ZMod 8) (0 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I) (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 J) ee) (fuseCol (7 : ZMod 8) (0 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_5_7 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 0) (ri (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I) (ri (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb5_7_0_1 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_0 (fuseRow ((5 : ZMod 8) + 7) (0 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb5_7_0_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, -1], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb5_7_0_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, -1], [0, 0, 0, 0]]]

noncomputable def Xcb5_7_0_1 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb5_7_0_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_7_0_1 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb5_7_0_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_7_0_1 : ∀ I J g, Xb5_7_0_1 I J g = Xcb5_7_0_1 I J g := by
  decide +kernel

theorem hYtabb5_7_0_1 : ∀ I J g, Yb5_7_0_1 I J g = Ycb5_7_0_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb5_7_0_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T5_7_0
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_7_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Xb5_7_0_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 hfuseZ_7_0 hfuseZ_5_7 (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Xcb5_7_0_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2)) (realRepBasis ((5 : ZMod 8) + 7 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_7_0_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Yb5_7_0_1 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hfuseZ_5_7 hfuseZ_4_0 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Ycb5_7_0_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2)) (realRepBasis ((5 : ZMod 8) + 7 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_7_0_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 0) (realGauge.gaugeSizeL 5 7 0).1 (realGauge.gaugeSizeL 5 7 0).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb5_7_0_1 TL5_7_0 YLb5_7_0_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc5_7_0_0 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_0 (fuseRow (7 : ZMod 8) (0 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I) (ro (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 J) ee) (fuseCol (7 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_5_7 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 0) (ri (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 I) (ri (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc5_7_0_0 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) I) = (lo (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (lo (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) I)
          * realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_0 (fuseRow ((5 : ZMod 8) + 7) (0 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc5_7_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc5_7_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcc5_7_0_0 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun r s g => coeffGet XLc5_7_0_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_7_0_0 : (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 0).val) → ℤ :=
  fun r s g => coeffGet YLc5_7_0_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_7_0_0 : ∀ I J g, Xc5_7_0_0 I J g = Xcc5_7_0_0 I J g := by
  decide +kernel

theorem hYtabc5_7_0_0 : ∀ I J g, Yc5_7_0_0 I J g = Ycc5_7_0_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc5_7_0_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))) * T5_7_0
      = ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_7_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Xc5_7_0_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 hfuseZ_7_0 hfuseZ_5_7 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Xcc5_7_0_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2)) (realRepBasis ((5 : ZMod 8) + 7 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_7_0_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Yc5_7_0_0 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hfuseZ_4_0 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 0)) Ycc5_7_0_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 0).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 0).2)) (realRepBasis ((5 : ZMod 8) + 7 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_7_0_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 0) (realGauge.gaugeSizeL 5 7 0).1 (realGauge.gaugeSizeL 5 7 0).2 ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc5_7_0_0 TL5_7_0 YLc5_7_0_0 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint5_7_0 (i : Fin (realRepDim (5 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) i)) * T5_7_0
      = ((sgn (realRepBasisParity (5 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T5_7_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (5 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h0]; exact hinta5_7_0_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h1]; exact hinta5_7_0_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h2]; exact hinta5_7_0_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h3]; exact hinta5_7_0_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h4]; exact hinta5_7_0_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h5]; exact hinta5_7_0_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h6]; exact hinta5_7_0_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h7]; exact hinta5_7_0_7

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint5_7_0 (i : Fin (realRepDim (7 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (7 : ZMod 8) i)) * T5_7_0
      = ((sgn (realRepBasisParity (7 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T5_7_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (7 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h0]; exact hintb5_7_0_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h1]; exact hintb5_7_0_1

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint5_7_0 (i : Fin (realRepDim (0 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) i)) * T5_7_0
      = ((sgn (realRepBasisParity (0 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T5_7_0 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 1 := i.isLt
  have h0 : (i : ℕ) = 0 := by omega
  rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) from Fin.ext h0]
  exact hintc5_7_0_0

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT5_7_0_mem_gInterSpace :
    gtOfT ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 T5_7_0 ∈ gInterSpace ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 hT5_7_0 hAint5_7_0 hBint5_7_0 hCint5_7_0

theorem gtOfT5_7_0_ne_zero : gtOfT ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 T5_7_0 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) hsz5_7_0 T5_7_0_ne_zero

theorem gInterSpace5_7_0_ne_bot : gInterSpace ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT5_7_0_mem_gInterSpace, gtOfT5_7_0_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_5_7_0 : gParity ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (0 : ZMod 8) gInterSpace5_7_0_ne_bot).symm

end Triple_5_7_0

/-! ### The triple `(5,7,1)`

`gaugeSizeL = gaugeSizeR = (1,1)`, `dim D_5 = 8`, certgen parity `0`; the transported connector literal. -/
section Triple_5_7_1
open Module
theorem hsz5_7_1 : realGauge.gaugeSizeR 5 7 1 = realGauge.gaugeSizeL 5 7 1 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`2 x 2 x 8`). -/
def TL5_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, -1, 1, 0], [0, 0, 0, 0, -1, 0, 0, 1]],
   [[0, -1, -1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0, 0]]]

/-- The same literal read at the composite frame `Fin 1 ⊕ Fin 1`. -/
noncomputable def Tc5_7_1 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun r s g => coeffGet TL5_7_1 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_5`. -/
noncomputable def T5_7_1 : ((realGauge.D ((5 : ZMod 8) + 7 + 1)).matrixSuper
    (realGauge.gaugeSizeL 5 7 1).1 (realGauge.gaugeSizeL 5 7 1).2).carrier :=
  matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Tc5_7_1

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT5_7_1 : T5_7_1 ∈ ((realGauge.D ((5 : ZMod 8) + 7 + 1)).matrixSuper
    (realGauge.gaugeSizeL 5 7 1).1 (realGauge.gaugeSizeL 5 7 1).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((5 : ZMod 8) + 7 + 1) Tc5_7_1 0 (by decide)

theorem T5_7_1_ne_zero : T5_7_1 ≠ 0 :=
  matOfCoeff_ne_zero ((5 : ZMod 8) + 7 + 1) Tc5_7_1 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨5, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa5_7_1_0 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (1 : ZMod 8)).1 (realSize (7 : ZMod 8) (1 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I)
          * realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_0 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 1) (ri (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I) (ri (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya5_7_1_0 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow ((5 : ZMod 8) + 7) (1 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa5_7_1_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa5_7_1_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca5_7_1_0 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_1_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_1_0 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_1_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_1_0 : ∀ I J g, Xa5_7_1_0 I J g = Xca5_7_1_0 I J g := by
  decide +kernel

theorem hYtaba5_7_1_0 : ∀ I J g, Ya5_7_1_0 I J g = Yca5_7_1_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta5_7_1_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_1
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_7_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Xa5_7_1_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 hfuseZ_5_0 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Xca5_7_1_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2)) (realRepBasis ((5 : ZMod 8) + 7 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_1_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Ya5_7_1_0 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hfuseZ_5_7 hfuseZ_4_1 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Yca5_7_1_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2)) (realRepBasis ((5 : ZMod 8) + 7 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_1_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 1) (realGauge.gaugeSizeL 5 7 1).1 (realGauge.gaugeSizeL 5 7 1).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_7_1_0 TL5_7_1 YLa5_7_1_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa5_7_1_1 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (1 : ZMod 8)).1 (realSize (7 : ZMod 8) (1 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I)
          * realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_0 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 1) (ri (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I) (ri (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 1) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya5_7_1_1 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow ((5 : ZMod 8) + 7) (1 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa5_7_1_1 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa5_7_1_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca5_7_1_1 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_1_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_1_1 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_1_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_1_1 : ∀ I J g, Xa5_7_1_1 I J g = Xca5_7_1_1 I J g := by
  decide +kernel

theorem hYtaba5_7_1_1 : ∀ I J g, Ya5_7_1_1 I J g = Yca5_7_1_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta5_7_1_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_1
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_7_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Xa5_7_1_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 hfuseZ_5_0 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Xca5_7_1_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2)) (realRepBasis ((5 : ZMod 8) + 7 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_1_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Ya5_7_1_1 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hfuseZ_5_7 hfuseZ_4_1 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Yca5_7_1_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2)) (realRepBasis ((5 : ZMod 8) + 7 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_1_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 1) (realGauge.gaugeSizeL 5 7 1).1 (realGauge.gaugeSizeL 5 7 1).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_7_1_1 TL5_7_1 YLa5_7_1_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa5_7_1_2 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (1 : ZMod 8)).1 (realSize (7 : ZMod 8) (1 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I)
          * realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_0 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 1) (ri (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I) (ri (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 1) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya5_7_1_2 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow ((5 : ZMod 8) + 7) (1 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa5_7_1_2 : List (List (List ℤ)) :=
  [[[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa5_7_1_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]],
   [[0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca5_7_1_2 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_1_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_1_2 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_1_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_1_2 : ∀ I J g, Xa5_7_1_2 I J g = Xca5_7_1_2 I J g := by
  decide +kernel

theorem hYtaba5_7_1_2 : ∀ I J g, Ya5_7_1_2 I J g = Yca5_7_1_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta5_7_1_2 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_1
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_7_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Xa5_7_1_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 hfuseZ_5_0 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Xca5_7_1_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2)) (realRepBasis ((5 : ZMod 8) + 7 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_1_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Ya5_7_1_2 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hfuseZ_5_7 hfuseZ_4_1 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Yca5_7_1_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2)) (realRepBasis ((5 : ZMod 8) + 7 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_1_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 1) (realGauge.gaugeSizeL 5 7 1).1 (realGauge.gaugeSizeL 5 7 1).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_7_1_2 TL5_7_1 YLa5_7_1_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa5_7_1_3 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (1 : ZMod 8)).1 (realSize (7 : ZMod 8) (1 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I)
          * realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_0 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 1) (ri (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I) (ri (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 1) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya5_7_1_3 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow ((5 : ZMod 8) + 7) (1 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa5_7_1_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa5_7_1_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]]]

noncomputable def Xca5_7_1_3 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_1_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_1_3 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_1_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_1_3 : ∀ I J g, Xa5_7_1_3 I J g = Xca5_7_1_3 I J g := by
  decide +kernel

theorem hYtaba5_7_1_3 : ∀ I J g, Ya5_7_1_3 I J g = Yca5_7_1_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta5_7_1_3 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_1
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_7_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Xa5_7_1_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 hfuseZ_5_0 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Xca5_7_1_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2)) (realRepBasis ((5 : ZMod 8) + 7 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_1_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Ya5_7_1_3 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hfuseZ_5_7 hfuseZ_4_1 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Yca5_7_1_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2)) (realRepBasis ((5 : ZMod 8) + 7 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_1_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 1) (realGauge.gaugeSizeL 5 7 1).1 (realGauge.gaugeSizeL 5 7 1).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_7_1_3 TL5_7_1 YLa5_7_1_3 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Xa5_7_1_4 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (1 : ZMod 8)).1 (realSize (7 : ZMod 8) (1 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I)
          * realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_0 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 1) (ri (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I) (ri (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 1) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Ya5_7_1_4 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow ((5 : ZMod 8) + 7) (1 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `4`, pre-tabulated. -/
def XLa5_7_1_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `4`, pre-tabulated. -/
def YLa5_7_1_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]],
   [[0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca5_7_1_4 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_1_4 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_1_4 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_1_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_1_4 : ∀ I J g, Xa5_7_1_4 I J g = Xca5_7_1_4 I J g := by
  decide +kernel

theorem hYtaba5_7_1_4 : ∀ I J g, Ya5_7_1_4 I J g = Yca5_7_1_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `4`** (Koszul sign `+1`). -/
theorem hinta5_7_1_4 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_1
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_7_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Xa5_7_1_4 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 hfuseZ_5_0 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Xca5_7_1_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2)) (realRepBasis ((5 : ZMod 8) + 7 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_1_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Ya5_7_1_4 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hfuseZ_5_7 hfuseZ_4_1 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Yca5_7_1_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2)) (realRepBasis ((5 : ZMod 8) + 7 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_1_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 1) (realGauge.gaugeSizeL 5 7 1).1 (realGauge.gaugeSizeL 5 7 1).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_7_1_4 TL5_7_1 YLa5_7_1_4 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Xa5_7_1_5 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (1 : ZMod 8)).1 (realSize (7 : ZMod 8) (1 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I)
          * realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_0 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 1) (ri (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I) (ri (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 1) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Ya5_7_1_5 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow ((5 : ZMod 8) + 7) (1 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `5`, pre-tabulated. -/
def XLa5_7_1_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0]]]

/-- Left route at the `a`-slot generator `5`, pre-tabulated. -/
def YLa5_7_1_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]]]

noncomputable def Xca5_7_1_5 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_1_5 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_1_5 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_1_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_1_5 : ∀ I J g, Xa5_7_1_5 I J g = Xca5_7_1_5 I J g := by
  decide +kernel

theorem hYtaba5_7_1_5 : ∀ I J g, Ya5_7_1_5 I J g = Yca5_7_1_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `5`** (Koszul sign `+1`). -/
theorem hinta5_7_1_5 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_1
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_7_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Xa5_7_1_5 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 hfuseZ_5_0 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Xca5_7_1_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2)) (realRepBasis ((5 : ZMod 8) + 7 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_1_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Ya5_7_1_5 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hfuseZ_5_7 hfuseZ_4_1 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Yca5_7_1_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2)) (realRepBasis ((5 : ZMod 8) + 7 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_1_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 1) (realGauge.gaugeSizeL 5 7 1).1 (realGauge.gaugeSizeL 5 7 1).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_7_1_5 TL5_7_1 YLa5_7_1_5 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Xa5_7_1_6 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (1 : ZMod 8)).1 (realSize (7 : ZMod 8) (1 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I)
          * realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_0 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 1) (ri (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I) (ri (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 1) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Ya5_7_1_6 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow ((5 : ZMod 8) + 7) (1 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `6`, pre-tabulated. -/
def XLa5_7_1_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]]]

/-- Left route at the `a`-slot generator `6`, pre-tabulated. -/
def YLa5_7_1_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0]]]

noncomputable def Xca5_7_1_6 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_1_6 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_1_6 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_1_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_1_6 : ∀ I J g, Xa5_7_1_6 I J g = Xca5_7_1_6 I J g := by
  decide +kernel

theorem hYtaba5_7_1_6 : ∀ I J g, Ya5_7_1_6 I J g = Yca5_7_1_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `6`** (Koszul sign `+1`). -/
theorem hinta5_7_1_6 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_1
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_7_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Xa5_7_1_6 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 hfuseZ_5_0 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Xca5_7_1_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2)) (realRepBasis ((5 : ZMod 8) + 7 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_1_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Ya5_7_1_6 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hfuseZ_5_7 hfuseZ_4_1 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Yca5_7_1_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2)) (realRepBasis ((5 : ZMod 8) + 7 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_1_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 1) (realGauge.gaugeSizeL 5 7 1).1 (realGauge.gaugeSizeL 5 7 1).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_7_1_6 TL5_7_1 YLa5_7_1_6 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Xa5_7_1_7 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (1 : ZMod 8)).1 (realSize (7 : ZMod 8) (1 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I)
          * realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_0 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 1) (ri (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I) (ri (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 1) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Ya5_7_1_7 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow ((5 : ZMod 8) + 7) (1 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `7`, pre-tabulated. -/
def XLa5_7_1_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]]]

/-- Left route at the `a`-slot generator `7`, pre-tabulated. -/
def YLa5_7_1_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0]],
   [[0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca5_7_1_7 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_1_7 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_1_7 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_1_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_1_7 : ∀ I J g, Xa5_7_1_7 I J g = Xca5_7_1_7 I J g := by
  decide +kernel

theorem hYtaba5_7_1_7 : ∀ I J g, Ya5_7_1_7 I J g = Yca5_7_1_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `7`** (Koszul sign `+1`). -/
theorem hinta5_7_1_7 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_1
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_7_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Xa5_7_1_7 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 hfuseZ_5_0 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Xca5_7_1_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2)) (realRepBasis ((5 : ZMod 8) + 7 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_1_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Ya5_7_1_7 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hfuseZ_5_7 hfuseZ_4_1 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Yca5_7_1_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2)) (realRepBasis ((5 : ZMod 8) + 7 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_1_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 1) (realGauge.gaugeSizeL 5 7 1).1 (realGauge.gaugeSizeL 5 7 1).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa5_7_1_7 TL5_7_1 YLa5_7_1_7 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb5_7_1_0 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_1 (fuseRow (7 : ZMod 8) (1 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I) (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 J) ee) (fuseCol (7 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_5_0 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 1) (ri (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I) (ri (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb5_7_1_0 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow ((5 : ZMod 8) + 7) (1 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb5_7_1_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb5_7_1_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb5_7_1_0 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun r s g => coeffGet XLb5_7_1_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_7_1_0 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun r s g => coeffGet YLb5_7_1_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_7_1_0 : ∀ I J g, Xb5_7_1_0 I J g = Xcb5_7_1_0 I J g := by
  decide +kernel

theorem hYtabb5_7_1_0 : ∀ I J g, Yb5_7_1_0 I J g = Ycb5_7_1_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb5_7_1_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T5_7_1
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_7_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Xb5_7_1_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 hfuseZ_7_1 hfuseZ_5_0 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Xcb5_7_1_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2)) (realRepBasis ((5 : ZMod 8) + 7 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_7_1_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Yb5_7_1_0 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hfuseZ_5_7 hfuseZ_4_1 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Ycb5_7_1_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2)) (realRepBasis ((5 : ZMod 8) + 7 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_7_1_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 1) (realGauge.gaugeSizeL 5 7 1).1 (realGauge.gaugeSizeL 5 7 1).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb5_7_1_0 TL5_7_1 YLb5_7_1_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb5_7_1_1 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_1 (fuseRow (7 : ZMod 8) (1 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I) (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 J) ee) (fuseCol (7 : ZMod 8) (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_5_0 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 1) (ri (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I) (ri (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb5_7_1_1 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow ((5 : ZMod 8) + 7) (1 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb5_7_1_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb5_7_1_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0]],
   [[0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb5_7_1_1 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun r s g => coeffGet XLb5_7_1_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_7_1_1 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun r s g => coeffGet YLb5_7_1_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_7_1_1 : ∀ I J g, Xb5_7_1_1 I J g = Xcb5_7_1_1 I J g := by
  decide +kernel

theorem hYtabb5_7_1_1 : ∀ I J g, Yb5_7_1_1 I J g = Ycb5_7_1_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb5_7_1_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T5_7_1
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_7_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Xb5_7_1_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 hfuseZ_7_1 hfuseZ_5_0 (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Xcb5_7_1_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2)) (realRepBasis ((5 : ZMod 8) + 7 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_7_1_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Yb5_7_1_1 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hfuseZ_5_7 hfuseZ_4_1 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Ycb5_7_1_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2)) (realRepBasis ((5 : ZMod 8) + 7 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_7_1_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 1) (realGauge.gaugeSizeL 5 7 1).1 (realGauge.gaugeSizeL 5 7 1).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb5_7_1_1 TL5_7_1 YLb5_7_1_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc5_7_1_0 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_1 (fuseRow (7 : ZMod 8) (1 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I) (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 J) ee) (fuseCol (7 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_5_0 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 1) (ri (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I) (ri (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc5_7_1_0 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) = (lo (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (lo (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I)
          * realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_1 (fuseRow ((5 : ZMod 8) + 7) (1 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc5_7_1_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc5_7_1_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcc5_7_1_0 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun r s g => coeffGet XLc5_7_1_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_7_1_0 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun r s g => coeffGet YLc5_7_1_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_7_1_0 : ∀ I J g, Xc5_7_1_0 I J g = Xcc5_7_1_0 I J g := by
  decide +kernel

theorem hYtabc5_7_1_0 : ∀ I J g, Yc5_7_1_0 I J g = Ycc5_7_1_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc5_7_1_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T5_7_1
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_7_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Xc5_7_1_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 hfuseZ_7_1 hfuseZ_5_0 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Xcc5_7_1_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2)) (realRepBasis ((5 : ZMod 8) + 7 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_7_1_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Yc5_7_1_0 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hfuseZ_4_1 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Ycc5_7_1_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2)) (realRepBasis ((5 : ZMod 8) + 7 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_7_1_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 1) (realGauge.gaugeSizeL 5 7 1).1 (realGauge.gaugeSizeL 5 7 1).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc5_7_1_0 TL5_7_1 YLc5_7_1_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc5_7_1_1 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_1 (fuseRow (7 : ZMod 8) (1 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I) (ro (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 J) ee) (fuseCol (7 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_5_0 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 1) (ri (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 I) (ri (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc5_7_1_1 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) = (lo (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (lo (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I)
          * realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_1 (fuseRow ((5 : ZMod 8) + 7) (1 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc5_7_1_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc5_7_1_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]]]

noncomputable def Xcc5_7_1_1 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun r s g => coeffGet XLc5_7_1_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_7_1_1 : (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 1).val) → ℤ :=
  fun r s g => coeffGet YLc5_7_1_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_7_1_1 : ∀ I J g, Xc5_7_1_1 I J g = Xcc5_7_1_1 I J g := by
  decide +kernel

theorem hYtabc5_7_1_1 : ∀ I J g, Yc5_7_1_1 I J g = Ycc5_7_1_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc5_7_1_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T5_7_1
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T5_7_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Xc5_7_1_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 hfuseZ_7_1 hfuseZ_5_0 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Xcc5_7_1_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2)) (realRepBasis ((5 : ZMod 8) + 7 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_7_1_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Yc5_7_1_1 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hfuseZ_4_1 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 1)) Ycc5_7_1_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 1).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 1).2)) (realRepBasis ((5 : ZMod 8) + 7 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_7_1_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 1) (realGauge.gaugeSizeL 5 7 1).1 (realGauge.gaugeSizeL 5 7 1).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc5_7_1_1 TL5_7_1 YLc5_7_1_1 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint5_7_1 (i : Fin (realRepDim (5 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) i)) * T5_7_1
      = ((sgn (realRepBasisParity (5 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T5_7_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (5 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h0]; exact hinta5_7_1_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h1]; exact hinta5_7_1_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h2]; exact hinta5_7_1_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h3]; exact hinta5_7_1_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h4]; exact hinta5_7_1_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h5]; exact hinta5_7_1_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h6]; exact hinta5_7_1_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h7]; exact hinta5_7_1_7

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint5_7_1 (i : Fin (realRepDim (7 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (7 : ZMod 8) i)) * T5_7_1
      = ((sgn (realRepBasisParity (7 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T5_7_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (7 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h0]; exact hintb5_7_1_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h1]; exact hintb5_7_1_1

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint5_7_1 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T5_7_1
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T5_7_1 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hintc5_7_1_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hintc5_7_1_1

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT5_7_1_mem_gInterSpace :
    gtOfT ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 T5_7_1 ∈ gInterSpace ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 hT5_7_1 hAint5_7_1 hBint5_7_1 hCint5_7_1

theorem gtOfT5_7_1_ne_zero : gtOfT ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 T5_7_1 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) hsz5_7_1 T5_7_1_ne_zero

theorem gInterSpace5_7_1_ne_bot : gInterSpace ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT5_7_1_mem_gInterSpace, gtOfT5_7_1_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_5_7_1 : gParity ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (1 : ZMod 8) gInterSpace5_7_1_ne_bot).symm

end Triple_5_7_1

/-! ### The triple `(5,7,2)`

`gaugeSizeL = gaugeSizeR = (2,2)`, `dim D_6 = 4`, certgen parity `1`; the transported connector literal. -/
section Triple_5_7_2
open Module
theorem hsz5_7_2 : realGauge.gaugeSizeR 5 7 2 = realGauge.gaugeSizeL 5 7 2 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`4 x 4 x 4`). -/
def TL5_7_2 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0]]]

/-- The same literal read at the composite frame `Fin 2 ⊕ Fin 2`. -/
noncomputable def Tc5_7_2 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet TL5_7_2 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_6`. -/
noncomputable def T5_7_2 : ((realGauge.D ((5 : ZMod 8) + 7 + 2)).matrixSuper
    (realGauge.gaugeSizeL 5 7 2).1 (realGauge.gaugeSizeL 5 7 2).2).carrier :=
  matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Tc5_7_2

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT5_7_2 : T5_7_2 ∈ ((realGauge.D ((5 : ZMod 8) + 7 + 2)).matrixSuper
    (realGauge.gaugeSizeL 5 7 2).1 (realGauge.gaugeSizeL 5 7 2).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((5 : ZMod 8) + 7 + 2) Tc5_7_2 1 (by decide)

theorem T5_7_2_ne_zero : T5_7_2 ≠ 0 :=
  matOfCoeff_ne_zero ((5 : ZMod 8) + 7 + 2) Tc5_7_2 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨1, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa5_7_2_0 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (2 : ZMod 8)).1 (realSize (7 : ZMod 8) (2 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I)
          * realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 2) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya5_7_2_0 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_2 (fuseRow ((5 : ZMod 8) + 7) (2 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa5_7_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa5_7_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xca5_7_2_0 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_2_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_2_0 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_2_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_2_0 : ∀ I J g, Xa5_7_2_0 I J g = Xca5_7_2_0 I J g := by
  decide +kernel

theorem hYtaba5_7_2_0 : ∀ I J g, Ya5_7_2_0 I J g = Yca5_7_2_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta5_7_2_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_2
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xa5_7_2_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 hfuseZ_5_1 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xca5_7_2_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_2_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Ya5_7_2_0 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hfuseZ_5_7 hfuseZ_4_2 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Yca5_7_2_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_2_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 2) (realGauge.gaugeSizeL 5 7 2).1 (realGauge.gaugeSizeL 5 7 2).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_2_0 TL5_7_2 YLa5_7_2_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa5_7_2_1 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (2 : ZMod 8)).1 (realSize (7 : ZMod 8) (2 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I)
          * realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 2) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 2) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya5_7_2_1 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_2 (fuseRow ((5 : ZMod 8) + 7) (2 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa5_7_2_1 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa5_7_2_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca5_7_2_1 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_2_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_2_1 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_2_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_2_1 : ∀ I J g, Xa5_7_2_1 I J g = Xca5_7_2_1 I J g := by
  decide +kernel

theorem hYtaba5_7_2_1 : ∀ I J g, Ya5_7_2_1 I J g = Yca5_7_2_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `-1`). -/
theorem hinta5_7_2_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_2
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xa5_7_2_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 hfuseZ_5_1 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xca5_7_2_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_2_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Ya5_7_2_1 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hfuseZ_5_7 hfuseZ_4_2 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Yca5_7_2_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_2_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 2) (realGauge.gaugeSizeL 5 7 2).1 (realGauge.gaugeSizeL 5 7 2).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_2_1 TL5_7_2 YLa5_7_2_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa5_7_2_2 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (2 : ZMod 8)).1 (realSize (7 : ZMod 8) (2 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I)
          * realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 2) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 2) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya5_7_2_2 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_2 (fuseRow ((5 : ZMod 8) + 7) (2 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa5_7_2_2 : List (List (List ℤ)) :=
  [[[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa5_7_2_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca5_7_2_2 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_2_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_2_2 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_2_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_2_2 : ∀ I J g, Xa5_7_2_2 I J g = Xca5_7_2_2 I J g := by
  decide +kernel

theorem hYtaba5_7_2_2 : ∀ I J g, Ya5_7_2_2 I J g = Yca5_7_2_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `-1`). -/
theorem hinta5_7_2_2 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_2
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xa5_7_2_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 hfuseZ_5_1 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xca5_7_2_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_2_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Ya5_7_2_2 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hfuseZ_5_7 hfuseZ_4_2 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Yca5_7_2_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_2_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 2) (realGauge.gaugeSizeL 5 7 2).1 (realGauge.gaugeSizeL 5 7 2).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_2_2 TL5_7_2 YLa5_7_2_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa5_7_2_3 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (2 : ZMod 8)).1 (realSize (7 : ZMod 8) (2 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I)
          * realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 2) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 2) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya5_7_2_3 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_2 (fuseRow ((5 : ZMod 8) + 7) (2 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa5_7_2_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa5_7_2_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]]]

noncomputable def Xca5_7_2_3 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_2_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_2_3 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_2_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_2_3 : ∀ I J g, Xa5_7_2_3 I J g = Xca5_7_2_3 I J g := by
  decide +kernel

theorem hYtaba5_7_2_3 : ∀ I J g, Ya5_7_2_3 I J g = Yca5_7_2_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta5_7_2_3 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_2
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xa5_7_2_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 hfuseZ_5_1 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xca5_7_2_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_2_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Ya5_7_2_3 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hfuseZ_5_7 hfuseZ_4_2 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Yca5_7_2_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_2_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 2) (realGauge.gaugeSizeL 5 7 2).1 (realGauge.gaugeSizeL 5 7 2).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_2_3 TL5_7_2 YLa5_7_2_3 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Xa5_7_2_4 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (2 : ZMod 8)).1 (realSize (7 : ZMod 8) (2 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I)
          * realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 2) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 2) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Ya5_7_2_4 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_2 (fuseRow ((5 : ZMod 8) + 7) (2 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `4`, pre-tabulated. -/
def XLa5_7_2_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `4`, pre-tabulated. -/
def YLa5_7_2_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]]]

noncomputable def Xca5_7_2_4 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_2_4 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_2_4 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_2_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_2_4 : ∀ I J g, Xa5_7_2_4 I J g = Xca5_7_2_4 I J g := by
  decide +kernel

theorem hYtaba5_7_2_4 : ∀ I J g, Ya5_7_2_4 I J g = Yca5_7_2_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `4`** (Koszul sign `-1`). -/
theorem hinta5_7_2_4 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_2
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xa5_7_2_4 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 hfuseZ_5_1 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xca5_7_2_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_2_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Ya5_7_2_4 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hfuseZ_5_7 hfuseZ_4_2 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Yca5_7_2_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_2_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 2) (realGauge.gaugeSizeL 5 7 2).1 (realGauge.gaugeSizeL 5 7 2).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_2_4 TL5_7_2 YLa5_7_2_4 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Xa5_7_2_5 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (2 : ZMod 8)).1 (realSize (7 : ZMod 8) (2 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I)
          * realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 2) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 2) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Ya5_7_2_5 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_2 (fuseRow ((5 : ZMod 8) + 7) (2 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `5`, pre-tabulated. -/
def XLa5_7_2_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0]],
   [[0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `5`, pre-tabulated. -/
def YLa5_7_2_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0]],
   [[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca5_7_2_5 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_2_5 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_2_5 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_2_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_2_5 : ∀ I J g, Xa5_7_2_5 I J g = Xca5_7_2_5 I J g := by
  decide +kernel

theorem hYtaba5_7_2_5 : ∀ I J g, Ya5_7_2_5 I J g = Yca5_7_2_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `5`** (Koszul sign `+1`). -/
theorem hinta5_7_2_5 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_2
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xa5_7_2_5 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 hfuseZ_5_1 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xca5_7_2_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_2_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Ya5_7_2_5 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hfuseZ_5_7 hfuseZ_4_2 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Yca5_7_2_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_2_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 2) (realGauge.gaugeSizeL 5 7 2).1 (realGauge.gaugeSizeL 5 7 2).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_2_5 TL5_7_2 YLa5_7_2_5 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Xa5_7_2_6 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (2 : ZMod 8)).1 (realSize (7 : ZMod 8) (2 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I)
          * realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 2) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 2) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Ya5_7_2_6 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_2 (fuseRow ((5 : ZMod 8) + 7) (2 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `6`, pre-tabulated. -/
def XLa5_7_2_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `6`, pre-tabulated. -/
def YLa5_7_2_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca5_7_2_6 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_2_6 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_2_6 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_2_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_2_6 : ∀ I J g, Xa5_7_2_6 I J g = Xca5_7_2_6 I J g := by
  decide +kernel

theorem hYtaba5_7_2_6 : ∀ I J g, Ya5_7_2_6 I J g = Yca5_7_2_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `6`** (Koszul sign `+1`). -/
theorem hinta5_7_2_6 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_2
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xa5_7_2_6 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 hfuseZ_5_1 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xca5_7_2_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_2_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Ya5_7_2_6 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hfuseZ_5_7 hfuseZ_4_2 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Yca5_7_2_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_2_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 2) (realGauge.gaugeSizeL 5 7 2).1 (realGauge.gaugeSizeL 5 7 2).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_2_6 TL5_7_2 YLa5_7_2_6 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Xa5_7_2_7 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (2 : ZMod 8)).1 (realSize (7 : ZMod 8) (2 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I)
          * realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 2) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 2) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Ya5_7_2_7 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_2 (fuseRow ((5 : ZMod 8) + 7) (2 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `7`, pre-tabulated. -/
def XLa5_7_2_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1]],
   [[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `7`, pre-tabulated. -/
def YLa5_7_2_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca5_7_2_7 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_2_7 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_2_7 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_2_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_2_7 : ∀ I J g, Xa5_7_2_7 I J g = Xca5_7_2_7 I J g := by
  decide +kernel

theorem hYtaba5_7_2_7 : ∀ I J g, Ya5_7_2_7 I J g = Yca5_7_2_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `7`** (Koszul sign `-1`). -/
theorem hinta5_7_2_7 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_2
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xa5_7_2_7 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 hfuseZ_5_1 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xca5_7_2_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_2_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Ya5_7_2_7 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hfuseZ_5_7 hfuseZ_4_2 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Yca5_7_2_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_2_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 2) (realGauge.gaugeSizeL 5 7 2).1 (realGauge.gaugeSizeL 5 7 2).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_2_7 TL5_7_2 YLa5_7_2_7 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb5_7_2_0 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_2 (fuseRow (7 : ZMod 8) (2 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) ee) (fuseCol (7 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 2) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb5_7_2_0 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_2 (fuseRow ((5 : ZMod 8) + 7) (2 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb5_7_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb5_7_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcb5_7_2_0 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb5_7_2_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_7_2_0 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb5_7_2_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_7_2_0 : ∀ I J g, Xb5_7_2_0 I J g = Xcb5_7_2_0 I J g := by
  decide +kernel

theorem hYtabb5_7_2_0 : ∀ I J g, Yb5_7_2_0 I J g = Ycb5_7_2_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb5_7_2_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T5_7_2
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xb5_7_2_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 hfuseZ_7_2 hfuseZ_5_1 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xcb5_7_2_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_7_2_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Yb5_7_2_0 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hfuseZ_5_7 hfuseZ_4_2 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Ycb5_7_2_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_7_2_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 2) (realGauge.gaugeSizeL 5 7 2).1 (realGauge.gaugeSizeL 5 7 2).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb5_7_2_0 TL5_7_2 YLb5_7_2_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb5_7_2_1 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_2 (fuseRow (7 : ZMod 8) (2 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) ee) (fuseCol (7 : ZMod 8) (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 2) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb5_7_2_1 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_2 (fuseRow ((5 : ZMod 8) + 7) (2 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb5_7_2_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb5_7_2_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb5_7_2_1 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb5_7_2_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_7_2_1 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb5_7_2_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_7_2_1 : ∀ I J g, Xb5_7_2_1 I J g = Xcb5_7_2_1 I J g := by
  decide +kernel

theorem hYtabb5_7_2_1 : ∀ I J g, Yb5_7_2_1 I J g = Ycb5_7_2_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintb5_7_2_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T5_7_2
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xb5_7_2_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 hfuseZ_7_2 hfuseZ_5_1 (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xcb5_7_2_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_7_2_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Yb5_7_2_1 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hfuseZ_5_7 hfuseZ_4_2 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Ycb5_7_2_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_7_2_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 2) (realGauge.gaugeSizeL 5 7 2).1 (realGauge.gaugeSizeL 5 7 2).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb5_7_2_1 TL5_7_2 YLb5_7_2_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc5_7_2_0 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_2 (fuseRow (7 : ZMod 8) (2 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) ee) (fuseCol (7 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 2) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc5_7_2_0 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) = (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_2 (fuseRow ((5 : ZMod 8) + 7) (2 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc5_7_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc5_7_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcc5_7_2_0 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc5_7_2_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_7_2_0 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc5_7_2_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_7_2_0 : ∀ I J g, Xc5_7_2_0 I J g = Xcc5_7_2_0 I J g := by
  decide +kernel

theorem hYtabc5_7_2_0 : ∀ I J g, Yc5_7_2_0 I J g = Ycc5_7_2_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc5_7_2_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T5_7_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xc5_7_2_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 hfuseZ_7_2 hfuseZ_5_1 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xcc5_7_2_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_7_2_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Yc5_7_2_0 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hfuseZ_4_2 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Ycc5_7_2_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_7_2_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 2) (realGauge.gaugeSizeL 5 7 2).1 (realGauge.gaugeSizeL 5 7 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_7_2_0 TL5_7_2 YLc5_7_2_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc5_7_2_1 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_2 (fuseRow (7 : ZMod 8) (2 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) ee) (fuseCol (7 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 2) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc5_7_2_1 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) = (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_2 (fuseRow ((5 : ZMod 8) + 7) (2 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc5_7_2_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc5_7_2_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1]],
   [[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc5_7_2_1 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc5_7_2_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_7_2_1 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc5_7_2_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_7_2_1 : ∀ I J g, Xc5_7_2_1 I J g = Xcc5_7_2_1 I J g := by
  decide +kernel

theorem hYtabc5_7_2_1 : ∀ I J g, Yc5_7_2_1 I J g = Ycc5_7_2_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintc5_7_2_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T5_7_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xc5_7_2_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 hfuseZ_7_2 hfuseZ_5_1 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xcc5_7_2_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_7_2_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Yc5_7_2_1 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hfuseZ_4_2 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Ycc5_7_2_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_7_2_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 2) (realGauge.gaugeSizeL 5 7 2).1 (realGauge.gaugeSizeL 5 7 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_7_2_1 TL5_7_2 YLc5_7_2_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc5_7_2_2 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_2 (fuseRow (7 : ZMod 8) (2 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) ee) (fuseCol (7 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 2) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc5_7_2_2 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) = (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_2 (fuseRow ((5 : ZMod 8) + 7) (2 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc5_7_2_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc5_7_2_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc5_7_2_2 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc5_7_2_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_7_2_2 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc5_7_2_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_7_2_2 : ∀ I J g, Xc5_7_2_2 I J g = Xcc5_7_2_2 I J g := by
  decide +kernel

theorem hYtabc5_7_2_2 : ∀ I J g, Yc5_7_2_2 I J g = Ycc5_7_2_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintc5_7_2_2 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T5_7_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xc5_7_2_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 hfuseZ_7_2 hfuseZ_5_1 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xcc5_7_2_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_7_2_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Yc5_7_2_2 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hfuseZ_4_2 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Ycc5_7_2_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_7_2_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 2) (realGauge.gaugeSizeL 5 7 2).1 (realGauge.gaugeSizeL 5 7 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_7_2_2 TL5_7_2 YLc5_7_2_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc5_7_2_3 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_2 (fuseRow (7 : ZMod 8) (2 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) (ro (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) ee) (fuseCol (7 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 2) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 I) (ri (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc5_7_2_3 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) = (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (lo (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_2 (fuseRow ((5 : ZMod 8) + 7) (2 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc5_7_2_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc5_7_2_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1]]]

noncomputable def Xcc5_7_2_3 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc5_7_2_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_7_2_3 : (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc5_7_2_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_7_2_3 : ∀ I J g, Xc5_7_2_3 I J g = Xcc5_7_2_3 I J g := by
  decide +kernel

theorem hYtabc5_7_2_3 : ∀ I J g, Yc5_7_2_3 I J g = Ycc5_7_2_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc5_7_2_3 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T5_7_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xc5_7_2_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 hfuseZ_7_2 hfuseZ_5_1 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Xcc5_7_2_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_7_2_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Yc5_7_2_3 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hfuseZ_4_2 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 2)) Ycc5_7_2_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 2).2)) (realRepBasis ((5 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_7_2_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 2) (realGauge.gaugeSizeL 5 7 2).1 (realGauge.gaugeSizeL 5 7 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_7_2_3 TL5_7_2 YLc5_7_2_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint5_7_2 (i : Fin (realRepDim (5 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) i)) * T5_7_2
      = ((sgn (realRepBasisParity (5 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T5_7_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h0]; exact hinta5_7_2_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h1]; exact hinta5_7_2_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h2]; exact hinta5_7_2_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h3]; exact hinta5_7_2_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h4]; exact hinta5_7_2_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h5]; exact hinta5_7_2_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h6]; exact hinta5_7_2_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h7]; exact hinta5_7_2_7

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint5_7_2 (i : Fin (realRepDim (7 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) i)) * T5_7_2
      = ((sgn (realRepBasisParity (7 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T5_7_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h0]; exact hintb5_7_2_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h1]; exact hintb5_7_2_1

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint5_7_2 (i : Fin (realRepDim (2 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) i)) * T5_7_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T5_7_2 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h0]; exact hintc5_7_2_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h1]; exact hintc5_7_2_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h2]; exact hintc5_7_2_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h3]; exact hintc5_7_2_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT5_7_2_mem_gInterSpace :
    gtOfT ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 T5_7_2 ∈ gInterSpace ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 hT5_7_2 hAint5_7_2 hBint5_7_2 hCint5_7_2

theorem gtOfT5_7_2_ne_zero : gtOfT ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 T5_7_2 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz5_7_2 T5_7_2_ne_zero

theorem gInterSpace5_7_2_ne_bot : gInterSpace ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT5_7_2_mem_gInterSpace, gtOfT5_7_2_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_5_7_2 : gParity ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) gInterSpace5_7_2_ne_bot).symm

end Triple_5_7_2

/-! ### The triple `(5,7,3)`

`gaugeSizeL = gaugeSizeR = (4,4)`, `dim D_7 = 2`, certgen parity `1`; the transported connector literal. -/
section Triple_5_7_3
open Module
theorem hsz5_7_3 : realGauge.gaugeSizeR 5 7 3 = realGauge.gaugeSizeL 5 7 3 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`8 x 8 x 2`). -/
def TL5_7_3 : List (List (List ℤ)) :=
  [[[0, 1], [0, 1], [0, -1], [0, -1], [1, 0], [1, 0], [-1, 0], [-1, 0]],
   [[0, 1], [0, 1], [0, 1], [0, 1], [-1, 0], [-1, 0], [-1, 0], [-1, 0]],
   [[0, -1], [0, 1], [0, 1], [0, -1], [-1, 0], [1, 0], [1, 0], [-1, 0]],
   [[0, 1], [0, -1], [0, 1], [0, -1], [-1, 0], [1, 0], [-1, 0], [1, 0]],
   [[1, 0], [-1, 0], [-1, 0], [1, 0], [0, -1], [0, 1], [0, 1], [0, -1]],
   [[1, 0], [-1, 0], [1, 0], [-1, 0], [0, 1], [0, -1], [0, 1], [0, -1]],
   [[1, 0], [1, 0], [-1, 0], [-1, 0], [0, -1], [0, -1], [0, 1], [0, 1]],
   [[-1, 0], [-1, 0], [-1, 0], [-1, 0], [0, -1], [0, -1], [0, -1], [0, -1]]]

/-- The same literal read at the composite frame `Fin 4 ⊕ Fin 4`. -/
noncomputable def Tc5_7_3 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet TL5_7_3 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_7`. -/
noncomputable def T5_7_3 : ((realGauge.D ((5 : ZMod 8) + 7 + 3)).matrixSuper
    (realGauge.gaugeSizeL 5 7 3).1 (realGauge.gaugeSizeL 5 7 3).2).carrier :=
  matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Tc5_7_3

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT5_7_3 : T5_7_3 ∈ ((realGauge.D ((5 : ZMod 8) + 7 + 3)).matrixSuper
    (realGauge.gaugeSizeL 5 7 3).1 (realGauge.gaugeSizeL 5 7 3).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((5 : ZMod 8) + 7 + 3) Tc5_7_3 1 (by decide)

theorem T5_7_3_ne_zero : T5_7_3 ≠ 0 :=
  matOfCoeff_ne_zero ((5 : ZMod 8) + 7 + 3) Tc5_7_3 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨1, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa5_7_3_0 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (3 : ZMod 8)).1 (realSize (7 : ZMod 8) (3 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I)
          * realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 3) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya5_7_3_0 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((5 : ZMod 8) + 7) (3 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa5_7_3_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa5_7_3_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xca5_7_3_0 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_3_0 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_3_0 : ∀ I J g, Xa5_7_3_0 I J g = Xca5_7_3_0 I J g := by
  decide +kernel

theorem hYtaba5_7_3_0 : ∀ I J g, Ya5_7_3_0 I J g = Yca5_7_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta5_7_3_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_3
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xa5_7_3_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xca5_7_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Ya5_7_3_0 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_5_7 hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Yca5_7_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 5 7 3).1 (realGauge.gaugeSizeL 5 7 3).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_3_0 TL5_7_3 YLa5_7_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa5_7_3_1 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (3 : ZMod 8)).1 (realSize (7 : ZMod 8) (3 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I)
          * realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 3) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 3) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya5_7_3_1 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((5 : ZMod 8) + 7) (3 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa5_7_3_1 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa5_7_3_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca5_7_3_1 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_3_1 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_3_1 : ∀ I J g, Xa5_7_3_1 I J g = Xca5_7_3_1 I J g := by
  decide +kernel

theorem hYtaba5_7_3_1 : ∀ I J g, Ya5_7_3_1 I J g = Yca5_7_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `-1`). -/
theorem hinta5_7_3_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_3
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xa5_7_3_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 hfuseZ_5_2 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xca5_7_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Ya5_7_3_1 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_5_7 hfuseZ_4_3 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Yca5_7_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 5 7 3).1 (realGauge.gaugeSizeL 5 7 3).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_3_1 TL5_7_3 YLa5_7_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa5_7_3_2 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (3 : ZMod 8)).1 (realSize (7 : ZMod 8) (3 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I)
          * realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 3) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 3) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya5_7_3_2 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((5 : ZMod 8) + 7) (3 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa5_7_3_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa5_7_3_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]]]

noncomputable def Xca5_7_3_2 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_3_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_3_2 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_3_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_3_2 : ∀ I J g, Xa5_7_3_2 I J g = Xca5_7_3_2 I J g := by
  decide +kernel

theorem hYtaba5_7_3_2 : ∀ I J g, Ya5_7_3_2 I J g = Yca5_7_3_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `-1`). -/
theorem hinta5_7_3_2 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_3
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xa5_7_3_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 hfuseZ_5_2 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xca5_7_3_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_3_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Ya5_7_3_2 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_5_7 hfuseZ_4_3 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Yca5_7_3_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_3_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 5 7 3).1 (realGauge.gaugeSizeL 5 7 3).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_3_2 TL5_7_3 YLa5_7_3_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa5_7_3_3 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (3 : ZMod 8)).1 (realSize (7 : ZMod 8) (3 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I)
          * realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 3) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 3) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya5_7_3_3 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((5 : ZMod 8) + 7) (3 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa5_7_3_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa5_7_3_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca5_7_3_3 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_3_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_3_3 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_3_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_3_3 : ∀ I J g, Xa5_7_3_3 I J g = Xca5_7_3_3 I J g := by
  decide +kernel

theorem hYtaba5_7_3_3 : ∀ I J g, Ya5_7_3_3 I J g = Yca5_7_3_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta5_7_3_3 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_3
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xa5_7_3_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 hfuseZ_5_2 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xca5_7_3_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_3_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Ya5_7_3_3 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_5_7 hfuseZ_4_3 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Yca5_7_3_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_3_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 5 7 3).1 (realGauge.gaugeSizeL 5 7 3).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_3_3 TL5_7_3 YLa5_7_3_3 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Xa5_7_3_4 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (3 : ZMod 8)).1 (realSize (7 : ZMod 8) (3 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I)
          * realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 3) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 3) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Ya5_7_3_4 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((5 : ZMod 8) + 7) (3 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `4`, pre-tabulated. -/
def XLa5_7_3_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `4`, pre-tabulated. -/
def YLa5_7_3_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca5_7_3_4 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_3_4 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_3_4 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_3_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_3_4 : ∀ I J g, Xa5_7_3_4 I J g = Xca5_7_3_4 I J g := by
  decide +kernel

theorem hYtaba5_7_3_4 : ∀ I J g, Ya5_7_3_4 I J g = Yca5_7_3_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `4`** (Koszul sign `-1`). -/
theorem hinta5_7_3_4 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_3
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xa5_7_3_4 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 hfuseZ_5_2 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xca5_7_3_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_3_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Ya5_7_3_4 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_5_7 hfuseZ_4_3 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Yca5_7_3_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_3_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 5 7 3).1 (realGauge.gaugeSizeL 5 7 3).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_3_4 TL5_7_3 YLa5_7_3_4 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Xa5_7_3_5 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (3 : ZMod 8)).1 (realSize (7 : ZMod 8) (3 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I)
          * realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 3) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 3) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Ya5_7_3_5 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((5 : ZMod 8) + 7) (3 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `5`, pre-tabulated. -/
def XLa5_7_3_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `5`, pre-tabulated. -/
def YLa5_7_3_5 : List (List (List ℤ)) :=
  [[[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]]]

noncomputable def Xca5_7_3_5 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_3_5 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_3_5 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_3_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_3_5 : ∀ I J g, Xa5_7_3_5 I J g = Xca5_7_3_5 I J g := by
  decide +kernel

theorem hYtaba5_7_3_5 : ∀ I J g, Ya5_7_3_5 I J g = Yca5_7_3_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `5`** (Koszul sign `+1`). -/
theorem hinta5_7_3_5 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_3
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xa5_7_3_5 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 hfuseZ_5_2 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xca5_7_3_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_3_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Ya5_7_3_5 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_5_7 hfuseZ_4_3 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Yca5_7_3_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_3_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 5 7 3).1 (realGauge.gaugeSizeL 5 7 3).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_3_5 TL5_7_3 YLa5_7_3_5 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Xa5_7_3_6 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (3 : ZMod 8)).1 (realSize (7 : ZMod 8) (3 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I)
          * realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 3) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 3) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Ya5_7_3_6 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((5 : ZMod 8) + 7) (3 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `6`, pre-tabulated. -/
def XLa5_7_3_6 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `6`, pre-tabulated. -/
def YLa5_7_3_6 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca5_7_3_6 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_3_6 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_3_6 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_3_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_3_6 : ∀ I J g, Xa5_7_3_6 I J g = Xca5_7_3_6 I J g := by
  decide +kernel

theorem hYtaba5_7_3_6 : ∀ I J g, Ya5_7_3_6 I J g = Yca5_7_3_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `6`** (Koszul sign `+1`). -/
theorem hinta5_7_3_6 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_3
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xa5_7_3_6 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 hfuseZ_5_2 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xca5_7_3_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_3_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Ya5_7_3_6 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_5_7 hfuseZ_4_3 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Yca5_7_3_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_3_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 5 7 3).1 (realGauge.gaugeSizeL 5 7 3).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_3_6 TL5_7_3 YLa5_7_3_6 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Xa5_7_3_7 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (3 : ZMod 8)).1 (realSize (7 : ZMod 8) (3 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I)
          * realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 3) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 3) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Ya5_7_3_7 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((5 : ZMod 8) + 7) (3 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `7`, pre-tabulated. -/
def XLa5_7_3_7 : List (List (List ℤ)) :=
  [[[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]]]

/-- Left route at the `a`-slot generator `7`, pre-tabulated. -/
def YLa5_7_3_7 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca5_7_3_7 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_3_7 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_3_7 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_3_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_3_7 : ∀ I J g, Xa5_7_3_7 I J g = Xca5_7_3_7 I J g := by
  decide +kernel

theorem hYtaba5_7_3_7 : ∀ I J g, Ya5_7_3_7 I J g = Yca5_7_3_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `7`** (Koszul sign `-1`). -/
theorem hinta5_7_3_7 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_3
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xa5_7_3_7 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 hfuseZ_5_2 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xca5_7_3_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_3_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Ya5_7_3_7 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_5_7 hfuseZ_4_3 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Yca5_7_3_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_3_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 5 7 3).1 (realGauge.gaugeSizeL 5 7 3).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_3_7 TL5_7_3 YLa5_7_3_7 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb5_7_3_0 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_3 (fuseRow (7 : ZMod 8) (3 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) ee) (fuseCol (7 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 3) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb5_7_3_0 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((5 : ZMod 8) + 7) (3 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb5_7_3_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb5_7_3_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcb5_7_3_0 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb5_7_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_7_3_0 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb5_7_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_7_3_0 : ∀ I J g, Xb5_7_3_0 I J g = Xcb5_7_3_0 I J g := by
  decide +kernel

theorem hYtabb5_7_3_0 : ∀ I J g, Yb5_7_3_0 I J g = Ycb5_7_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb5_7_3_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T5_7_3
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xb5_7_3_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 hfuseZ_7_3 hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xcb5_7_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_7_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Yb5_7_3_0 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_5_7 hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Ycb5_7_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_7_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 5 7 3).1 (realGauge.gaugeSizeL 5 7 3).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb5_7_3_0 TL5_7_3 YLb5_7_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb5_7_3_1 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_3 (fuseRow (7 : ZMod 8) (3 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) ee) (fuseCol (7 : ZMod 8) (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 3) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb5_7_3_1 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((5 : ZMod 8) + 7) (3 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb5_7_3_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb5_7_3_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb5_7_3_1 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb5_7_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_7_3_1 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb5_7_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_7_3_1 : ∀ I J g, Xb5_7_3_1 I J g = Xcb5_7_3_1 I J g := by
  decide +kernel

theorem hYtabb5_7_3_1 : ∀ I J g, Yb5_7_3_1 I J g = Ycb5_7_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintb5_7_3_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T5_7_3
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xb5_7_3_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 hfuseZ_7_3 hfuseZ_5_2 (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xcb5_7_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_7_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Yb5_7_3_1 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_5_7 hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Ycb5_7_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_7_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 5 7 3).1 (realGauge.gaugeSizeL 5 7 3).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb5_7_3_1 TL5_7_3 YLb5_7_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc5_7_3_0 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_3 (fuseRow (7 : ZMod 8) (3 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) ee) (fuseCol (7 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 3) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc5_7_3_0 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) = (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow ((5 : ZMod 8) + 7) (3 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc5_7_3_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc5_7_3_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcc5_7_3_0 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc5_7_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_7_3_0 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc5_7_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_7_3_0 : ∀ I J g, Xc5_7_3_0 I J g = Xcc5_7_3_0 I J g := by
  decide +kernel

theorem hYtabc5_7_3_0 : ∀ I J g, Yc5_7_3_0 I J g = Ycc5_7_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc5_7_3_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T5_7_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xc5_7_3_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 hfuseZ_7_3 hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xcc5_7_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_7_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Yc5_7_3_0 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Ycc5_7_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_7_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 5 7 3).1 (realGauge.gaugeSizeL 5 7 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_7_3_0 TL5_7_3 YLc5_7_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc5_7_3_1 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_3 (fuseRow (7 : ZMod 8) (3 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) ee) (fuseCol (7 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 3) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc5_7_3_1 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) = (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow ((5 : ZMod 8) + 7) (3 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc5_7_3_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc5_7_3_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]]]

noncomputable def Xcc5_7_3_1 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc5_7_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_7_3_1 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc5_7_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_7_3_1 : ∀ I J g, Xc5_7_3_1 I J g = Xcc5_7_3_1 I J g := by
  decide +kernel

theorem hYtabc5_7_3_1 : ∀ I J g, Yc5_7_3_1 I J g = Ycc5_7_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintc5_7_3_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T5_7_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xc5_7_3_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 hfuseZ_7_3 hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xcc5_7_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_7_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Yc5_7_3_1 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Ycc5_7_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_7_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 5 7 3).1 (realGauge.gaugeSizeL 5 7 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_7_3_1 TL5_7_3 YLc5_7_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc5_7_3_2 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_3 (fuseRow (7 : ZMod 8) (3 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) ee) (fuseCol (7 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 3) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc5_7_3_2 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) = (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow ((5 : ZMod 8) + 7) (3 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc5_7_3_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc5_7_3_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc5_7_3_2 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc5_7_3_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_7_3_2 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc5_7_3_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_7_3_2 : ∀ I J g, Xc5_7_3_2 I J g = Xcc5_7_3_2 I J g := by
  decide +kernel

theorem hYtabc5_7_3_2 : ∀ I J g, Yc5_7_3_2 I J g = Ycc5_7_3_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintc5_7_3_2 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T5_7_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xc5_7_3_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 hfuseZ_7_3 hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xcc5_7_3_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_7_3_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Yc5_7_3_2 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Ycc5_7_3_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_7_3_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 5 7 3).1 (realGauge.gaugeSizeL 5 7 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_7_3_2 TL5_7_3 YLc5_7_3_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc5_7_3_3 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_3 (fuseRow (7 : ZMod 8) (3 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) ee) (fuseCol (7 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 3) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc5_7_3_3 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) = (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow ((5 : ZMod 8) + 7) (3 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc5_7_3_3 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc5_7_3_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc5_7_3_3 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc5_7_3_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_7_3_3 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc5_7_3_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_7_3_3 : ∀ I J g, Xc5_7_3_3 I J g = Xcc5_7_3_3 I J g := by
  decide +kernel

theorem hYtabc5_7_3_3 : ∀ I J g, Yc5_7_3_3 I J g = Ycc5_7_3_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc5_7_3_3 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T5_7_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xc5_7_3_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 hfuseZ_7_3 hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xcc5_7_3_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_7_3_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Yc5_7_3_3 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Ycc5_7_3_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_7_3_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 5 7 3).1 (realGauge.gaugeSizeL 5 7 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_7_3_3 TL5_7_3 YLc5_7_3_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Xc5_7_3_4 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_3 (fuseRow (7 : ZMod 8) (3 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) ee) (fuseCol (7 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 3) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Yc5_7_3_4 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) = (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow ((5 : ZMod 8) + 7) (3 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `4`, pre-tabulated. -/
def XLc5_7_3_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `4`, pre-tabulated. -/
def YLc5_7_3_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc5_7_3_4 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc5_7_3_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_7_3_4 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc5_7_3_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_7_3_4 : ∀ I J g, Xc5_7_3_4 I J g = Xcc5_7_3_4 I J g := by
  decide +kernel

theorem hYtabc5_7_3_4 : ∀ I J g, Yc5_7_3_4 I J g = Ycc5_7_3_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `4`** (Koszul sign `-1`). -/
theorem hintc5_7_3_4 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T5_7_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xc5_7_3_4 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 hfuseZ_7_3 hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xcc5_7_3_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_7_3_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Yc5_7_3_4 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Ycc5_7_3_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_7_3_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 5 7 3).1 (realGauge.gaugeSizeL 5 7 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_7_3_4 TL5_7_3 YLc5_7_3_4 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Xc5_7_3_5 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_3 (fuseRow (7 : ZMod 8) (3 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) ee) (fuseCol (7 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 3) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Yc5_7_3_5 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) = (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow ((5 : ZMod 8) + 7) (3 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `5`, pre-tabulated. -/
def XLc5_7_3_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `5`, pre-tabulated. -/
def YLc5_7_3_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc5_7_3_5 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc5_7_3_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_7_3_5 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc5_7_3_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_7_3_5 : ∀ I J g, Xc5_7_3_5 I J g = Xcc5_7_3_5 I J g := by
  decide +kernel

theorem hYtabc5_7_3_5 : ∀ I J g, Yc5_7_3_5 I J g = Ycc5_7_3_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintc5_7_3_5 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T5_7_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xc5_7_3_5 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 hfuseZ_7_3 hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xcc5_7_3_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_7_3_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Yc5_7_3_5 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Ycc5_7_3_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_7_3_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 5 7 3).1 (realGauge.gaugeSizeL 5 7 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_7_3_5 TL5_7_3 YLc5_7_3_5 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Xc5_7_3_6 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_3 (fuseRow (7 : ZMod 8) (3 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) ee) (fuseCol (7 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 3) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Yc5_7_3_6 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) = (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow ((5 : ZMod 8) + 7) (3 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `6`, pre-tabulated. -/
def XLc5_7_3_6 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `6`, pre-tabulated. -/
def YLc5_7_3_6 : List (List (List ℤ)) :=
  [[[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]]]

noncomputable def Xcc5_7_3_6 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc5_7_3_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_7_3_6 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc5_7_3_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_7_3_6 : ∀ I J g, Xc5_7_3_6 I J g = Xcc5_7_3_6 I J g := by
  decide +kernel

theorem hYtabc5_7_3_6 : ∀ I J g, Yc5_7_3_6 I J g = Ycc5_7_3_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintc5_7_3_6 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T5_7_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xc5_7_3_6 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 hfuseZ_7_3 hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xcc5_7_3_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_7_3_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Yc5_7_3_6 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Ycc5_7_3_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_7_3_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 5 7 3).1 (realGauge.gaugeSizeL 5 7 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_7_3_6 TL5_7_3 YLc5_7_3_6 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Xc5_7_3_7 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_3 (fuseRow (7 : ZMod 8) (3 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ro (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) ee) (fuseCol (7 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 3) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 I) (ri (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Yc5_7_3_7 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) = (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (lo (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow ((5 : ZMod 8) + 7) (3 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `7`, pre-tabulated. -/
def XLc5_7_3_7 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `7`, pre-tabulated. -/
def YLc5_7_3_7 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]]]

noncomputable def Xcc5_7_3_7 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc5_7_3_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_7_3_7 : (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc5_7_3_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_7_3_7 : ∀ I J g, Xc5_7_3_7 I J g = Xcc5_7_3_7 I J g := by
  decide +kernel

theorem hYtabc5_7_3_7 : ∀ I J g, Yc5_7_3_7 I J g = Ycc5_7_3_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `7`** (Koszul sign `-1`). -/
theorem hintc5_7_3_7 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T5_7_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xc5_7_3_7 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 hfuseZ_7_3 hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Xcc5_7_3_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_7_3_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Yc5_7_3_7 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 3)) Ycc5_7_3_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 3).2)) (realRepBasis ((5 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_7_3_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 5 7 3).1 (realGauge.gaugeSizeL 5 7 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_7_3_7 TL5_7_3 YLc5_7_3_7 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint5_7_3 (i : Fin (realRepDim (5 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) i)) * T5_7_3
      = ((sgn (realRepBasisParity (5 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T5_7_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h0]; exact hinta5_7_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h1]; exact hinta5_7_3_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h2]; exact hinta5_7_3_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h3]; exact hinta5_7_3_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h4]; exact hinta5_7_3_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h5]; exact hinta5_7_3_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h6]; exact hinta5_7_3_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h7]; exact hinta5_7_3_7

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint5_7_3 (i : Fin (realRepDim (7 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) i)) * T5_7_3
      = ((sgn (realRepBasisParity (7 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T5_7_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h0]; exact hintb5_7_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h1]; exact hintb5_7_3_1

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint5_7_3 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T5_7_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T5_7_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hintc5_7_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hintc5_7_3_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hintc5_7_3_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hintc5_7_3_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hintc5_7_3_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hintc5_7_3_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hintc5_7_3_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hintc5_7_3_7

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT5_7_3_mem_gInterSpace :
    gtOfT ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 T5_7_3 ∈ gInterSpace ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 hT5_7_3 hAint5_7_3 hBint5_7_3 hCint5_7_3

theorem gtOfT5_7_3_ne_zero : gtOfT ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 T5_7_3 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz5_7_3 T5_7_3_ne_zero

theorem gInterSpace5_7_3_ne_bot : gInterSpace ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT5_7_3_mem_gInterSpace, gtOfT5_7_3_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_5_7_3 : gParity ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) gInterSpace5_7_3_ne_bot).symm

end Triple_5_7_3

/-! ### The triple `(5,7,4)`

`gaugeSizeL = gaugeSizeR = (4,4)`, `dim D_0 = 1`, certgen parity `1`; the transported connector literal. -/
section Triple_5_7_4
open Module
theorem hsz5_7_4 : realGauge.gaugeSizeR 5 7 4 = realGauge.gaugeSizeL 5 7 4 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`8 x 8 x 1`). -/
def TL5_7_4 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [1], [1]],
   [[0], [0], [0], [0], [0], [0], [1], [-1]],
   [[0], [0], [0], [0], [1], [-1], [0], [0]],
   [[0], [0], [0], [0], [-1], [-1], [0], [0]],
   [[0], [0], [-1], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [-1], [0], [0], [0], [0]],
   [[1], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [1], [0], [0], [0], [0], [0], [0]]]

/-- The same literal read at the composite frame `Fin 4 ⊕ Fin 4`. -/
noncomputable def Tc5_7_4 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet TL5_7_4 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_0`. -/
noncomputable def T5_7_4 : ((realGauge.D ((5 : ZMod 8) + 7 + 4)).matrixSuper
    (realGauge.gaugeSizeL 5 7 4).1 (realGauge.gaugeSizeL 5 7 4).2).carrier :=
  matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Tc5_7_4

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT5_7_4 : T5_7_4 ∈ ((realGauge.D ((5 : ZMod 8) + 7 + 4)).matrixSuper
    (realGauge.gaugeSizeL 5 7 4).1 (realGauge.gaugeSizeL 5 7 4).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((5 : ZMod 8) + 7 + 4) Tc5_7_4 1 (by decide)

theorem T5_7_4_ne_zero : T5_7_4 ≠ 0 :=
  matOfCoeff_ne_zero ((5 : ZMod 8) + 7 + 4) Tc5_7_4 (Sum.inl ⟨0, by decide⟩) (Sum.inr ⟨2, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa5_7_4_0 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (4 : ZMod 8)).1 (realSize (7 : ZMod 8) (4 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I)
          * realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 4) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya5_7_4_0 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((5 : ZMod 8) + 7) (4 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa5_7_4_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa5_7_4_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xca5_7_4_0 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_4_0 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_4_0 : ∀ I J g, Xa5_7_4_0 I J g = Xca5_7_4_0 I J g := by
  decide +kernel

theorem hYtaba5_7_4_0 : ∀ I J g, Ya5_7_4_0 I J g = Yca5_7_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta5_7_4_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_4
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_4 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xa5_7_4_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xca5_7_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Ya5_7_4_0 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hfuseZ_5_7 hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Yca5_7_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 4) (realGauge.gaugeSizeL 5 7 4).1 (realGauge.gaugeSizeL 5 7 4).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_4_0 TL5_7_4 YLa5_7_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa5_7_4_1 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (4 : ZMod 8)).1 (realSize (7 : ZMod 8) (4 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I)
          * realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 4) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 4) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya5_7_4_1 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((5 : ZMod 8) + 7) (4 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa5_7_4_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa5_7_4_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]]]

noncomputable def Xca5_7_4_1 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_4_1 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_4_1 : ∀ I J g, Xa5_7_4_1 I J g = Xca5_7_4_1 I J g := by
  decide +kernel

theorem hYtaba5_7_4_1 : ∀ I J g, Ya5_7_4_1 I J g = Yca5_7_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `-1`). -/
theorem hinta5_7_4_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_4
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_4 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xa5_7_4_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 hfuseZ_5_3 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xca5_7_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Ya5_7_4_1 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hfuseZ_5_7 hfuseZ_4_4 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Yca5_7_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 4) (realGauge.gaugeSizeL 5 7 4).1 (realGauge.gaugeSizeL 5 7 4).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_4_1 TL5_7_4 YLa5_7_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa5_7_4_2 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (4 : ZMod 8)).1 (realSize (7 : ZMod 8) (4 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I)
          * realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 4) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 4) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya5_7_4_2 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((5 : ZMod 8) + 7) (4 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa5_7_4_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa5_7_4_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]]]

noncomputable def Xca5_7_4_2 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_4_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_4_2 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_4_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_4_2 : ∀ I J g, Xa5_7_4_2 I J g = Xca5_7_4_2 I J g := by
  decide +kernel

theorem hYtaba5_7_4_2 : ∀ I J g, Ya5_7_4_2 I J g = Yca5_7_4_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `-1`). -/
theorem hinta5_7_4_2 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_4
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_4 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xa5_7_4_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 hfuseZ_5_3 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xca5_7_4_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_4_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Ya5_7_4_2 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hfuseZ_5_7 hfuseZ_4_4 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Yca5_7_4_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_4_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 4) (realGauge.gaugeSizeL 5 7 4).1 (realGauge.gaugeSizeL 5 7 4).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_4_2 TL5_7_4 YLa5_7_4_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa5_7_4_3 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (4 : ZMod 8)).1 (realSize (7 : ZMod 8) (4 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I)
          * realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 4) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 4) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya5_7_4_3 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((5 : ZMod 8) + 7) (4 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa5_7_4_3 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa5_7_4_3 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]]]

noncomputable def Xca5_7_4_3 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_4_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_4_3 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_4_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_4_3 : ∀ I J g, Xa5_7_4_3 I J g = Xca5_7_4_3 I J g := by
  decide +kernel

theorem hYtaba5_7_4_3 : ∀ I J g, Ya5_7_4_3 I J g = Yca5_7_4_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta5_7_4_3 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_4
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_4 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xa5_7_4_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 hfuseZ_5_3 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xca5_7_4_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_4_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Ya5_7_4_3 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hfuseZ_5_7 hfuseZ_4_4 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Yca5_7_4_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_4_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 4) (realGauge.gaugeSizeL 5 7 4).1 (realGauge.gaugeSizeL 5 7 4).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_4_3 TL5_7_4 YLa5_7_4_3 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Xa5_7_4_4 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (4 : ZMod 8)).1 (realSize (7 : ZMod 8) (4 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I)
          * realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 4) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 4) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Ya5_7_4_4 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((5 : ZMod 8) + 7) (4 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `4`, pre-tabulated. -/
def XLa5_7_4_4 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `4`, pre-tabulated. -/
def YLa5_7_4_4 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xca5_7_4_4 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_4_4 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_4_4 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_4_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_4_4 : ∀ I J g, Xa5_7_4_4 I J g = Xca5_7_4_4 I J g := by
  decide +kernel

theorem hYtaba5_7_4_4 : ∀ I J g, Ya5_7_4_4 I J g = Yca5_7_4_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `4`** (Koszul sign `-1`). -/
theorem hinta5_7_4_4 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_4
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_4 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xa5_7_4_4 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 hfuseZ_5_3 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xca5_7_4_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_4_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Ya5_7_4_4 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hfuseZ_5_7 hfuseZ_4_4 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Yca5_7_4_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_4_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 4) (realGauge.gaugeSizeL 5 7 4).1 (realGauge.gaugeSizeL 5 7 4).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_4_4 TL5_7_4 YLa5_7_4_4 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Xa5_7_4_5 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (4 : ZMod 8)).1 (realSize (7 : ZMod 8) (4 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I)
          * realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 4) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 4) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Ya5_7_4_5 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((5 : ZMod 8) + 7) (4 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `5`, pre-tabulated. -/
def XLa5_7_4_5 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]]]

/-- Left route at the `a`-slot generator `5`, pre-tabulated. -/
def YLa5_7_4_5 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]]]

noncomputable def Xca5_7_4_5 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_4_5 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_4_5 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_4_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_4_5 : ∀ I J g, Xa5_7_4_5 I J g = Xca5_7_4_5 I J g := by
  decide +kernel

theorem hYtaba5_7_4_5 : ∀ I J g, Ya5_7_4_5 I J g = Yca5_7_4_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `5`** (Koszul sign `+1`). -/
theorem hinta5_7_4_5 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_4
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_4 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xa5_7_4_5 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 hfuseZ_5_3 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xca5_7_4_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_4_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Ya5_7_4_5 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hfuseZ_5_7 hfuseZ_4_4 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Yca5_7_4_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_4_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 4) (realGauge.gaugeSizeL 5 7 4).1 (realGauge.gaugeSizeL 5 7 4).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_4_5 TL5_7_4 YLa5_7_4_5 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Xa5_7_4_6 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (4 : ZMod 8)).1 (realSize (7 : ZMod 8) (4 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I)
          * realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 4) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 4) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Ya5_7_4_6 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((5 : ZMod 8) + 7) (4 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `6`, pre-tabulated. -/
def XLa5_7_4_6 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `6`, pre-tabulated. -/
def YLa5_7_4_6 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

noncomputable def Xca5_7_4_6 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_4_6 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_4_6 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_4_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_4_6 : ∀ I J g, Xa5_7_4_6 I J g = Xca5_7_4_6 I J g := by
  decide +kernel

theorem hYtaba5_7_4_6 : ∀ I J g, Ya5_7_4_6 I J g = Yca5_7_4_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `6`** (Koszul sign `+1`). -/
theorem hinta5_7_4_6 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_4
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_4 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xa5_7_4_6 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 hfuseZ_5_3 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xca5_7_4_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_4_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Ya5_7_4_6 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hfuseZ_5_7 hfuseZ_4_4 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Yca5_7_4_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_4_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 4) (realGauge.gaugeSizeL 5 7 4).1 (realGauge.gaugeSizeL 5 7 4).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_4_6 TL5_7_4 YLa5_7_4_6 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Xa5_7_4_7 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (4 : ZMod 8)).1 (realSize (7 : ZMod 8) (4 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I)
          * realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 4) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 4) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Ya5_7_4_7 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((5 : ZMod 8) + 7) (4 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `7`, pre-tabulated. -/
def XLa5_7_4_7 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `7`, pre-tabulated. -/
def YLa5_7_4_7 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xca5_7_4_7 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_4_7 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_4_7 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_4_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_4_7 : ∀ I J g, Xa5_7_4_7 I J g = Xca5_7_4_7 I J g := by
  decide +kernel

theorem hYtaba5_7_4_7 : ∀ I J g, Ya5_7_4_7 I J g = Yca5_7_4_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `7`** (Koszul sign `-1`). -/
theorem hinta5_7_4_7 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_4
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_4 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xa5_7_4_7 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 hfuseZ_5_3 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xca5_7_4_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_4_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Ya5_7_4_7 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hfuseZ_5_7 hfuseZ_4_4 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Yca5_7_4_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_4_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 4) (realGauge.gaugeSizeL 5 7 4).1 (realGauge.gaugeSizeL 5 7 4).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_4_7 TL5_7_4 YLa5_7_4_7 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb5_7_4_0 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_4 (fuseRow (7 : ZMod 8) (4 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) ee) (fuseCol (7 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 4) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb5_7_4_0 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((5 : ZMod 8) + 7) (4 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb5_7_4_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb5_7_4_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xcb5_7_4_0 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb5_7_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_7_4_0 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb5_7_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_7_4_0 : ∀ I J g, Xb5_7_4_0 I J g = Xcb5_7_4_0 I J g := by
  decide +kernel

theorem hYtabb5_7_4_0 : ∀ I J g, Yb5_7_4_0 I J g = Ycb5_7_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb5_7_4_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T5_7_4
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_4 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xb5_7_4_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 hfuseZ_7_4 hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xcb5_7_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_7_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Yb5_7_4_0 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hfuseZ_5_7 hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Ycb5_7_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_7_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 4) (realGauge.gaugeSizeL 5 7 4).1 (realGauge.gaugeSizeL 5 7 4).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb5_7_4_0 TL5_7_4 YLb5_7_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb5_7_4_1 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_4 (fuseRow (7 : ZMod 8) (4 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) ee) (fuseCol (7 : ZMod 8) (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 4) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb5_7_4_1 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((5 : ZMod 8) + 7) (4 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb5_7_4_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb5_7_4_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xcb5_7_4_1 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb5_7_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_7_4_1 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb5_7_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_7_4_1 : ∀ I J g, Xb5_7_4_1 I J g = Xcb5_7_4_1 I J g := by
  decide +kernel

theorem hYtabb5_7_4_1 : ∀ I J g, Yb5_7_4_1 I J g = Ycb5_7_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintb5_7_4_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T5_7_4
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_4 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xb5_7_4_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 hfuseZ_7_4 hfuseZ_5_3 (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xcb5_7_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_7_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Yb5_7_4_1 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hfuseZ_5_7 hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Ycb5_7_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_7_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 4) (realGauge.gaugeSizeL 5 7 4).1 (realGauge.gaugeSizeL 5 7 4).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb5_7_4_1 TL5_7_4 YLb5_7_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc5_7_4_0 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_4 (fuseRow (7 : ZMod 8) (4 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) ee) (fuseCol (7 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 4) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc5_7_4_0 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) = (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_4 (fuseRow ((5 : ZMod 8) + 7) (4 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc5_7_4_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc5_7_4_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xcc5_7_4_0 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc5_7_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_7_4_0 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc5_7_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_7_4_0 : ∀ I J g, Xc5_7_4_0 I J g = Xcc5_7_4_0 I J g := by
  decide +kernel

theorem hYtabc5_7_4_0 : ∀ I J g, Yc5_7_4_0 I J g = Ycc5_7_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc5_7_4_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T5_7_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_4 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xc5_7_4_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 hfuseZ_7_4 hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xcc5_7_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_7_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Yc5_7_4_0 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Ycc5_7_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_7_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 4) (realGauge.gaugeSizeL 5 7 4).1 (realGauge.gaugeSizeL 5 7 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_7_4_0 TL5_7_4 YLc5_7_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc5_7_4_1 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_4 (fuseRow (7 : ZMod 8) (4 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) ee) (fuseCol (7 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 4) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc5_7_4_1 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) = (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_4 (fuseRow ((5 : ZMod 8) + 7) (4 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc5_7_4_1 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc5_7_4_1 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]]]

noncomputable def Xcc5_7_4_1 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc5_7_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_7_4_1 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc5_7_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_7_4_1 : ∀ I J g, Xc5_7_4_1 I J g = Xcc5_7_4_1 I J g := by
  decide +kernel

theorem hYtabc5_7_4_1 : ∀ I J g, Yc5_7_4_1 I J g = Ycc5_7_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc5_7_4_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T5_7_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_4 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xc5_7_4_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 hfuseZ_7_4 hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xcc5_7_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_7_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Yc5_7_4_1 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Ycc5_7_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_7_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 4) (realGauge.gaugeSizeL 5 7 4).1 (realGauge.gaugeSizeL 5 7 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_7_4_1 TL5_7_4 YLc5_7_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc5_7_4_2 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_4 (fuseRow (7 : ZMod 8) (4 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) ee) (fuseCol (7 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 4) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc5_7_4_2 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) = (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_4 (fuseRow ((5 : ZMod 8) + 7) (4 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc5_7_4_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc5_7_4_2 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]]]

noncomputable def Xcc5_7_4_2 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc5_7_4_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_7_4_2 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc5_7_4_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_7_4_2 : ∀ I J g, Xc5_7_4_2 I J g = Xcc5_7_4_2 I J g := by
  decide +kernel

theorem hYtabc5_7_4_2 : ∀ I J g, Yc5_7_4_2 I J g = Ycc5_7_4_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc5_7_4_2 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T5_7_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_4 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xc5_7_4_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 hfuseZ_7_4 hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xcc5_7_4_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_7_4_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Yc5_7_4_2 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Ycc5_7_4_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_7_4_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 4) (realGauge.gaugeSizeL 5 7 4).1 (realGauge.gaugeSizeL 5 7 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_7_4_2 TL5_7_4 YLc5_7_4_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc5_7_4_3 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_4 (fuseRow (7 : ZMod 8) (4 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) (ro (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) ee) (fuseCol (7 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 4) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 I) (ri (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc5_7_4_3 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) = (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (lo (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_4 (fuseRow ((5 : ZMod 8) + 7) (4 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc5_7_4_3 : List (List (List ℤ)) :=
  [[[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc5_7_4_3 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

noncomputable def Xcc5_7_4_3 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc5_7_4_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_7_4_3 : (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc5_7_4_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_7_4_3 : ∀ I J g, Xc5_7_4_3 I J g = Xcc5_7_4_3 I J g := by
  decide +kernel

theorem hYtabc5_7_4_3 : ∀ I J g, Yc5_7_4_3 I J g = Ycc5_7_4_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc5_7_4_3 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T5_7_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_4 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xc5_7_4_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 hfuseZ_7_4 hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Xcc5_7_4_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_7_4_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Yc5_7_4_3 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 4)) Ycc5_7_4_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 4).2)) (realRepBasis ((5 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_7_4_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 4) (realGauge.gaugeSizeL 5 7 4).1 (realGauge.gaugeSizeL 5 7 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_7_4_3 TL5_7_4 YLc5_7_4_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint5_7_4 (i : Fin (realRepDim (5 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) i)) * T5_7_4
      = ((sgn (realRepBasisParity (5 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T5_7_4 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h0]; exact hinta5_7_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h1]; exact hinta5_7_4_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h2]; exact hinta5_7_4_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h3]; exact hinta5_7_4_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h4]; exact hinta5_7_4_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h5]; exact hinta5_7_4_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h6]; exact hinta5_7_4_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h7]; exact hinta5_7_4_7

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint5_7_4 (i : Fin (realRepDim (7 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) i)) * T5_7_4
      = ((sgn (realRepBasisParity (7 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T5_7_4 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h0]; exact hintb5_7_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h1]; exact hintb5_7_4_1

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint5_7_4 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T5_7_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T5_7_4 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hintc5_7_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hintc5_7_4_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hintc5_7_4_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hintc5_7_4_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT5_7_4_mem_gInterSpace :
    gtOfT ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 T5_7_4 ∈ gInterSpace ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 hT5_7_4 hAint5_7_4 hBint5_7_4 hCint5_7_4

theorem gtOfT5_7_4_ne_zero : gtOfT ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 T5_7_4 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz5_7_4 T5_7_4_ne_zero

theorem gInterSpace5_7_4_ne_bot : gInterSpace ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT5_7_4_mem_gInterSpace, gtOfT5_7_4_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_5_7_4 : gParity ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) gInterSpace5_7_4_ne_bot).symm

end Triple_5_7_4

/-! ### The triple `(5,7,5)`

`gaugeSizeL = gaugeSizeR = (4,4)`, `dim D_1 = 2`, certgen parity `1`; the transported connector literal. -/
section Triple_5_7_5
open Module
theorem hsz5_7_5 : realGauge.gaugeSizeR 5 7 5 = realGauge.gaugeSizeL 5 7 5 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`8 x 8 x 2`). -/
def TL5_7_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 1], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, -1], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- The same literal read at the composite frame `Fin 4 ⊕ Fin 4`. -/
noncomputable def Tc5_7_5 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet TL5_7_5 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_1`. -/
noncomputable def T5_7_5 : ((realGauge.D ((5 : ZMod 8) + 7 + 5)).matrixSuper
    (realGauge.gaugeSizeL 5 7 5).1 (realGauge.gaugeSizeL 5 7 5).2).carrier :=
  matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Tc5_7_5

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT5_7_5 : T5_7_5 ∈ ((realGauge.D ((5 : ZMod 8) + 7 + 5)).matrixSuper
    (realGauge.gaugeSizeL 5 7 5).1 (realGauge.gaugeSizeL 5 7 5).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((5 : ZMod 8) + 7 + 5) Tc5_7_5 1 (by decide)

theorem T5_7_5_ne_zero : T5_7_5 ≠ 0 :=
  matOfCoeff_ne_zero ((5 : ZMod 8) + 7 + 5) Tc5_7_5 (Sum.inl ⟨0, by decide⟩) (Sum.inr ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa5_7_5_0 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (5 : ZMod 8)).1 (realSize (7 : ZMod 8) (5 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I)
          * realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_4 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 5) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya5_7_5_0 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((5 : ZMod 8) + 7) (5 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa5_7_5_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa5_7_5_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xca5_7_5_0 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_5_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_5_0 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_5_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_5_0 : ∀ I J g, Xa5_7_5_0 I J g = Xca5_7_5_0 I J g := by
  decide +kernel

theorem hYtaba5_7_5_0 : ∀ I J g, Ya5_7_5_0 I J g = Yca5_7_5_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta5_7_5_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_5 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xa5_7_5_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 hfuseZ_5_4 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xca5_7_5_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_5_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Ya5_7_5_0 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_5_7 hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Yca5_7_5_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_5_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 5 7 5).1 (realGauge.gaugeSizeL 5 7 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_5_0 TL5_7_5 YLa5_7_5_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa5_7_5_1 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (5 : ZMod 8)).1 (realSize (7 : ZMod 8) (5 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I)
          * realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_4 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 5) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 5) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya5_7_5_1 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((5 : ZMod 8) + 7) (5 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa5_7_5_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa5_7_5_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca5_7_5_1 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_5_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_5_1 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_5_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_5_1 : ∀ I J g, Xa5_7_5_1 I J g = Xca5_7_5_1 I J g := by
  decide +kernel

theorem hYtaba5_7_5_1 : ∀ I J g, Ya5_7_5_1 I J g = Yca5_7_5_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `-1`). -/
theorem hinta5_7_5_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_5 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xa5_7_5_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 hfuseZ_5_4 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xca5_7_5_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_5_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Ya5_7_5_1 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_5_7 hfuseZ_4_5 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Yca5_7_5_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_5_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 5 7 5).1 (realGauge.gaugeSizeL 5 7 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_5_1 TL5_7_5 YLa5_7_5_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa5_7_5_2 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (5 : ZMod 8)).1 (realSize (7 : ZMod 8) (5 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I)
          * realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_4 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 5) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 5) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya5_7_5_2 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((5 : ZMod 8) + 7) (5 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa5_7_5_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa5_7_5_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]]]

noncomputable def Xca5_7_5_2 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_5_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_5_2 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_5_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_5_2 : ∀ I J g, Xa5_7_5_2 I J g = Xca5_7_5_2 I J g := by
  decide +kernel

theorem hYtaba5_7_5_2 : ∀ I J g, Ya5_7_5_2 I J g = Yca5_7_5_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `-1`). -/
theorem hinta5_7_5_2 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_5 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xa5_7_5_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 hfuseZ_5_4 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xca5_7_5_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_5_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Ya5_7_5_2 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_5_7 hfuseZ_4_5 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Yca5_7_5_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_5_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 5 7 5).1 (realGauge.gaugeSizeL 5 7 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_5_2 TL5_7_5 YLa5_7_5_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa5_7_5_3 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (5 : ZMod 8)).1 (realSize (7 : ZMod 8) (5 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I)
          * realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_4 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 5) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 5) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya5_7_5_3 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((5 : ZMod 8) + 7) (5 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa5_7_5_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa5_7_5_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca5_7_5_3 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_5_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_5_3 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_5_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_5_3 : ∀ I J g, Xa5_7_5_3 I J g = Xca5_7_5_3 I J g := by
  decide +kernel

theorem hYtaba5_7_5_3 : ∀ I J g, Ya5_7_5_3 I J g = Yca5_7_5_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta5_7_5_3 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_5 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xa5_7_5_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 hfuseZ_5_4 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xca5_7_5_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_5_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Ya5_7_5_3 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_5_7 hfuseZ_4_5 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Yca5_7_5_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_5_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 5 7 5).1 (realGauge.gaugeSizeL 5 7 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_5_3 TL5_7_5 YLa5_7_5_3 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Xa5_7_5_4 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (5 : ZMod 8)).1 (realSize (7 : ZMod 8) (5 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I)
          * realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_4 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 5) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 5) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Ya5_7_5_4 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((5 : ZMod 8) + 7) (5 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `4`, pre-tabulated. -/
def XLa5_7_5_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `4`, pre-tabulated. -/
def YLa5_7_5_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca5_7_5_4 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_5_4 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_5_4 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_5_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_5_4 : ∀ I J g, Xa5_7_5_4 I J g = Xca5_7_5_4 I J g := by
  decide +kernel

theorem hYtaba5_7_5_4 : ∀ I J g, Ya5_7_5_4 I J g = Yca5_7_5_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `4`** (Koszul sign `-1`). -/
theorem hinta5_7_5_4 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_5 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xa5_7_5_4 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 hfuseZ_5_4 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xca5_7_5_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_5_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Ya5_7_5_4 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_5_7 hfuseZ_4_5 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Yca5_7_5_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_5_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 5 7 5).1 (realGauge.gaugeSizeL 5 7 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_5_4 TL5_7_5 YLa5_7_5_4 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Xa5_7_5_5 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (5 : ZMod 8)).1 (realSize (7 : ZMod 8) (5 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I)
          * realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_4 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 5) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 5) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Ya5_7_5_5 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((5 : ZMod 8) + 7) (5 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `5`, pre-tabulated. -/
def XLa5_7_5_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `5`, pre-tabulated. -/
def YLa5_7_5_5 : List (List (List ℤ)) :=
  [[[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]]]

noncomputable def Xca5_7_5_5 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_5_5 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_5_5 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_5_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_5_5 : ∀ I J g, Xa5_7_5_5 I J g = Xca5_7_5_5 I J g := by
  decide +kernel

theorem hYtaba5_7_5_5 : ∀ I J g, Ya5_7_5_5 I J g = Yca5_7_5_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `5`** (Koszul sign `+1`). -/
theorem hinta5_7_5_5 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_5 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xa5_7_5_5 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 hfuseZ_5_4 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xca5_7_5_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_5_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Ya5_7_5_5 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_5_7 hfuseZ_4_5 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Yca5_7_5_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_5_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 5 7 5).1 (realGauge.gaugeSizeL 5 7 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_5_5 TL5_7_5 YLa5_7_5_5 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Xa5_7_5_6 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (5 : ZMod 8)).1 (realSize (7 : ZMod 8) (5 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I)
          * realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_4 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 5) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 5) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Ya5_7_5_6 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((5 : ZMod 8) + 7) (5 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `6`, pre-tabulated. -/
def XLa5_7_5_6 : List (List (List ℤ)) :=
  [[[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `6`, pre-tabulated. -/
def YLa5_7_5_6 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca5_7_5_6 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_5_6 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_5_6 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_5_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_5_6 : ∀ I J g, Xa5_7_5_6 I J g = Xca5_7_5_6 I J g := by
  decide +kernel

theorem hYtaba5_7_5_6 : ∀ I J g, Ya5_7_5_6 I J g = Yca5_7_5_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `6`** (Koszul sign `+1`). -/
theorem hinta5_7_5_6 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_5 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xa5_7_5_6 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 hfuseZ_5_4 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xca5_7_5_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_5_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Ya5_7_5_6 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_5_7 hfuseZ_4_5 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Yca5_7_5_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_5_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 5 7 5).1 (realGauge.gaugeSizeL 5 7 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_5_6 TL5_7_5 YLa5_7_5_6 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Xa5_7_5_7 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) = (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (5 : ZMod 8)).1 (realSize (7 : ZMod 8) (5 : ZMod 8)).2 (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I)
          * realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_4 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 5) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 5) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Ya5_7_5_7 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((5 : ZMod 8) + 7) (5 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `7`, pre-tabulated. -/
def XLa5_7_5_7 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]]]

/-- Left route at the `a`-slot generator `7`, pre-tabulated. -/
def YLa5_7_5_7 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca5_7_5_7 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa5_7_5_7 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_7_5_7 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa5_7_5_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_7_5_7 : ∀ I J g, Xa5_7_5_7 I J g = Xca5_7_5_7 I J g := by
  decide +kernel

theorem hYtaba5_7_5_7 : ∀ I J g, Ya5_7_5_7 I J g = Yca5_7_5_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `7`** (Koszul sign `-1`). -/
theorem hinta5_7_5_7 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_5 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xa5_7_5_7 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 hfuseZ_5_4 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xca5_7_5_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_7_5_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Ya5_7_5_7 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_5_7 hfuseZ_4_5 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Yca5_7_5_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_7_5_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 5 7 5).1 (realGauge.gaugeSizeL 5 7 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_7_5_7 TL5_7_5 YLa5_7_5_7 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb5_7_5_0 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_5 (fuseRow (7 : ZMod 8) (5 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) ee) (fuseCol (7 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_5_4 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 5) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb5_7_5_0 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((5 : ZMod 8) + 7) (5 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb5_7_5_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb5_7_5_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcb5_7_5_0 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb5_7_5_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_7_5_0 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb5_7_5_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_7_5_0 : ∀ I J g, Xb5_7_5_0 I J g = Xcb5_7_5_0 I J g := by
  decide +kernel

theorem hYtabb5_7_5_0 : ∀ I J g, Yb5_7_5_0 I J g = Ycb5_7_5_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb5_7_5_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T5_7_5
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_5 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xb5_7_5_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 hfuseZ_7_5 hfuseZ_5_4 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xcb5_7_5_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_7_5_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Yb5_7_5_0 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_5_7 hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Ycb5_7_5_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_7_5_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 5 7 5).1 (realGauge.gaugeSizeL 5 7 5).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb5_7_5_0 TL5_7_5 YLb5_7_5_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb5_7_5_1 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_5 (fuseRow (7 : ZMod 8) (5 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) ee) (fuseCol (7 : ZMod 8) (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_5_4 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 5) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb5_7_5_1 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((5 : ZMod 8) + 7) (5 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb5_7_5_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb5_7_5_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb5_7_5_1 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb5_7_5_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_7_5_1 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb5_7_5_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_7_5_1 : ∀ I J g, Xb5_7_5_1 I J g = Xcb5_7_5_1 I J g := by
  decide +kernel

theorem hYtabb5_7_5_1 : ∀ I J g, Yb5_7_5_1 I J g = Ycb5_7_5_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintb5_7_5_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T5_7_5
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_5 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xb5_7_5_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 hfuseZ_7_5 hfuseZ_5_4 (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xcb5_7_5_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_7_5_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Yb5_7_5_1 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_5_7 hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Ycb5_7_5_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_7_5_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 5 7 5).1 (realGauge.gaugeSizeL 5 7 5).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb5_7_5_1 TL5_7_5 YLb5_7_5_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc5_7_5_0 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_5 (fuseRow (7 : ZMod 8) (5 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) ee) (fuseCol (7 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_5_4 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 5) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc5_7_5_0 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) = (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow ((5 : ZMod 8) + 7) (5 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc5_7_5_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc5_7_5_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcc5_7_5_0 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc5_7_5_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_7_5_0 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc5_7_5_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_7_5_0 : ∀ I J g, Xc5_7_5_0 I J g = Xcc5_7_5_0 I J g := by
  decide +kernel

theorem hYtabc5_7_5_0 : ∀ I J g, Yc5_7_5_0 I J g = Ycc5_7_5_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc5_7_5_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_5 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xc5_7_5_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 hfuseZ_7_5 hfuseZ_5_4 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xcc5_7_5_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_7_5_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Yc5_7_5_0 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Ycc5_7_5_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_7_5_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 5 7 5).1 (realGauge.gaugeSizeL 5 7 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_7_5_0 TL5_7_5 YLc5_7_5_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc5_7_5_1 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_5 (fuseRow (7 : ZMod 8) (5 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) ee) (fuseCol (7 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_5_4 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 5) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc5_7_5_1 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) = (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow ((5 : ZMod 8) + 7) (5 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc5_7_5_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc5_7_5_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]]]

noncomputable def Xcc5_7_5_1 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc5_7_5_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_7_5_1 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc5_7_5_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_7_5_1 : ∀ I J g, Xc5_7_5_1 I J g = Xcc5_7_5_1 I J g := by
  decide +kernel

theorem hYtabc5_7_5_1 : ∀ I J g, Yc5_7_5_1 I J g = Ycc5_7_5_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintc5_7_5_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_5 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xc5_7_5_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 hfuseZ_7_5 hfuseZ_5_4 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xcc5_7_5_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_7_5_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Yc5_7_5_1 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Ycc5_7_5_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_7_5_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 5 7 5).1 (realGauge.gaugeSizeL 5 7 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_7_5_1 TL5_7_5 YLc5_7_5_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc5_7_5_2 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_5 (fuseRow (7 : ZMod 8) (5 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) ee) (fuseCol (7 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_5_4 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 5) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc5_7_5_2 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) = (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow ((5 : ZMod 8) + 7) (5 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc5_7_5_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc5_7_5_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc5_7_5_2 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc5_7_5_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_7_5_2 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc5_7_5_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_7_5_2 : ∀ I J g, Xc5_7_5_2 I J g = Xcc5_7_5_2 I J g := by
  decide +kernel

theorem hYtabc5_7_5_2 : ∀ I J g, Yc5_7_5_2 I J g = Ycc5_7_5_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintc5_7_5_2 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_5 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xc5_7_5_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 hfuseZ_7_5 hfuseZ_5_4 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xcc5_7_5_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_7_5_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Yc5_7_5_2 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Ycc5_7_5_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_7_5_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 5 7 5).1 (realGauge.gaugeSizeL 5 7 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_7_5_2 TL5_7_5 YLc5_7_5_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc5_7_5_3 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_5 (fuseRow (7 : ZMod 8) (5 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) ee) (fuseCol (7 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_5_4 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 5) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc5_7_5_3 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) = (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow ((5 : ZMod 8) + 7) (5 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc5_7_5_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc5_7_5_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc5_7_5_3 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc5_7_5_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_7_5_3 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc5_7_5_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_7_5_3 : ∀ I J g, Xc5_7_5_3 I J g = Xcc5_7_5_3 I J g := by
  decide +kernel

theorem hYtabc5_7_5_3 : ∀ I J g, Yc5_7_5_3 I J g = Ycc5_7_5_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc5_7_5_3 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_5 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xc5_7_5_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 hfuseZ_7_5 hfuseZ_5_4 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xcc5_7_5_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_7_5_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Yc5_7_5_3 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Ycc5_7_5_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_7_5_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 5 7 5).1 (realGauge.gaugeSizeL 5 7 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_7_5_3 TL5_7_5 YLc5_7_5_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Xc5_7_5_4 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_5 (fuseRow (7 : ZMod 8) (5 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) ee) (fuseCol (7 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_5_4 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 5) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Yc5_7_5_4 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) = (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow ((5 : ZMod 8) + 7) (5 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `4`, pre-tabulated. -/
def XLc5_7_5_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `4`, pre-tabulated. -/
def YLc5_7_5_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc5_7_5_4 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc5_7_5_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_7_5_4 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc5_7_5_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_7_5_4 : ∀ I J g, Xc5_7_5_4 I J g = Xcc5_7_5_4 I J g := by
  decide +kernel

theorem hYtabc5_7_5_4 : ∀ I J g, Yc5_7_5_4 I J g = Ycc5_7_5_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `4`** (Koszul sign `-1`). -/
theorem hintc5_7_5_4 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_5 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xc5_7_5_4 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 hfuseZ_7_5 hfuseZ_5_4 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xcc5_7_5_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_7_5_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Yc5_7_5_4 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Ycc5_7_5_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_7_5_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 5 7 5).1 (realGauge.gaugeSizeL 5 7 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_7_5_4 TL5_7_5 YLc5_7_5_4 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Xc5_7_5_5 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_5 (fuseRow (7 : ZMod 8) (5 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) ee) (fuseCol (7 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_5_4 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 5) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Yc5_7_5_5 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) = (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow ((5 : ZMod 8) + 7) (5 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `5`, pre-tabulated. -/
def XLc5_7_5_5 : List (List (List ℤ)) :=
  [[[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `5`, pre-tabulated. -/
def YLc5_7_5_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc5_7_5_5 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc5_7_5_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_7_5_5 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc5_7_5_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_7_5_5 : ∀ I J g, Xc5_7_5_5 I J g = Xcc5_7_5_5 I J g := by
  decide +kernel

theorem hYtabc5_7_5_5 : ∀ I J g, Yc5_7_5_5 I J g = Ycc5_7_5_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintc5_7_5_5 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_5 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xc5_7_5_5 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 hfuseZ_7_5 hfuseZ_5_4 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xcc5_7_5_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_7_5_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Yc5_7_5_5 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Ycc5_7_5_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_7_5_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 5 7 5).1 (realGauge.gaugeSizeL 5 7 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_7_5_5 TL5_7_5 YLc5_7_5_5 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Xc5_7_5_6 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_5 (fuseRow (7 : ZMod 8) (5 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) ee) (fuseCol (7 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_5_4 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 5) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Yc5_7_5_6 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) = (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow ((5 : ZMod 8) + 7) (5 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `6`, pre-tabulated. -/
def XLc5_7_5_6 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `6`, pre-tabulated. -/
def YLc5_7_5_6 : List (List (List ℤ)) :=
  [[[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]]]

noncomputable def Xcc5_7_5_6 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc5_7_5_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_7_5_6 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc5_7_5_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_7_5_6 : ∀ I J g, Xc5_7_5_6 I J g = Xcc5_7_5_6 I J g := by
  decide +kernel

theorem hYtabc5_7_5_6 : ∀ I J g, Yc5_7_5_6 I J g = Ycc5_7_5_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintc5_7_5_6 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_5 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xc5_7_5_6 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 hfuseZ_7_5 hfuseZ_5_4 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xcc5_7_5_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_7_5_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Yc5_7_5_6 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Ycc5_7_5_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_7_5_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 5 7 5).1 (realGauge.gaugeSizeL 5 7 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_7_5_6 TL5_7_5 YLc5_7_5_6 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Xc5_7_5_7 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_5 (fuseRow (7 : ZMod 8) (5 : ZMod 8) (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ro (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) ee) (fuseCol (7 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_5_4 (fuseRow (5 : ZMod 8) ((7 : ZMod 8) + 5) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 I) (ri (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 J) g) (fuseCol (5 : ZMod 8) ((7 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Yc5_7_5_7 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) = (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (lo (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow ((5 : ZMod 8) + 7) (5 : ZMod 8) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 7) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `7`, pre-tabulated. -/
def XLc5_7_5_7 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `7`, pre-tabulated. -/
def YLc5_7_5_7 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]]]

noncomputable def Xcc5_7_5_7 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc5_7_5_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_7_5_7 : (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2) → Fin (realRepDim ((5 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc5_7_5_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_7_5_7 : ∀ I J g, Xc5_7_5_7 I J g = Xcc5_7_5_7 I J g := by
  decide +kernel

theorem hYtabc5_7_5_7 : ∀ I J g, Yc5_7_5_7 I J g = Ycc5_7_5_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `7`** (Koszul sign `-1`). -/
theorem hintc5_7_5_7 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_7_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_7_5 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xc5_7_5_7 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 hfuseZ_7_5 hfuseZ_5_4 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Xcc5_7_5_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_7_5_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Yc5_7_5_7 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 7 + 5)) Ycc5_7_5_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 5 7 5).2)) (realRepBasis ((5 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_7_5_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 5 7 5).1 (realGauge.gaugeSizeL 5 7 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_7_5_7 TL5_7_5 YLc5_7_5_7 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint5_7_5 (i : Fin (realRepDim (5 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) i)) * T5_7_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T5_7_5 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h0]; exact hinta5_7_5_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h1]; exact hinta5_7_5_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h2]; exact hinta5_7_5_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h3]; exact hinta5_7_5_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h4]; exact hinta5_7_5_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h5]; exact hinta5_7_5_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h6]; exact hinta5_7_5_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h7]; exact hinta5_7_5_7

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint5_7_5 (i : Fin (realRepDim (7 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) i)) * T5_7_5
      = ((sgn (realRepBasisParity (7 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T5_7_5 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h0]; exact hintb5_7_5_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h1]; exact hintb5_7_5_1

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint5_7_5 (i : Fin (realRepDim (5 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) i)) * T5_7_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T5_7_5 * (realGauge.gaugeRouteL (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h0]; exact hintc5_7_5_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h1]; exact hintc5_7_5_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h2]; exact hintc5_7_5_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h3]; exact hintc5_7_5_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h4]; exact hintc5_7_5_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h5]; exact hintc5_7_5_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h6]; exact hintc5_7_5_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h7]; exact hintc5_7_5_7

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT5_7_5_mem_gInterSpace :
    gtOfT ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 T5_7_5 ∈ gInterSpace ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 hT5_7_5 hAint5_7_5 hBint5_7_5 hCint5_7_5

theorem gtOfT5_7_5_ne_zero : gtOfT ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 T5_7_5 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz5_7_5 T5_7_5_ne_zero

theorem gInterSpace5_7_5_ne_bot : gInterSpace ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT5_7_5_mem_gInterSpace, gtOfT5_7_5_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_5_7_5 : gParity ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (5 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) gInterSpace5_7_5_ne_bot).symm

end Triple_5_7_5

end G5_21
end TripleCerts
end GaugeChi
end Superfusion

/-! ### Kernel self-check -/

#print axioms Superfusion.GaugeChi.TripleCerts.G5_21.gParity_5_7_0
#print axioms Superfusion.GaugeChi.TripleCerts.G5_21.gParity_5_7_1
#print axioms Superfusion.GaugeChi.TripleCerts.G5_21.gParity_5_7_2
#print axioms Superfusion.GaugeChi.TripleCerts.G5_21.gParity_5_7_3
#print axioms Superfusion.GaugeChi.TripleCerts.G5_21.gParity_5_7_4
#print axioms Superfusion.GaugeChi.TripleCerts.G5_21.gParity_5_7_5
