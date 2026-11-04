/-
Superfusion / GaugeChi / TripleCerts / G3_15

**GENERATED FILE — do not edit.**  Regenerate with

    python3 scripts/certgen/gen_triple_certs.py \
        --triples 3,1,3 3,1,4 3,1,5 3,1,6 3,1,7 3,2,0 \
        --module G3_15 \
        --out Superfusion/GaugeChi/TripleCerts/G3_15.lean

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

Triples (6): (3,1,3), (3,1,4), (3,1,5), (3,1,6), (3,1,7), (3,2,0).
Unit-slot triples (`a = 0` or `b = 0` or `c = 0`) in this batch: (3,2,0).
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
namespace G3_15

open Module

/-! ### The fusion shadows this batch uses (19 of the 64)

They are declared at the enclosing `TripleCerts` namespace by
`TripleCerts/FuseShadows.lean`, so the short names below resolve
unqualified and no `open` is needed:

  `fuseZ_1_3`, `fuseZ_1_4`, `fuseZ_1_5`, `fuseZ_1_6`, `fuseZ_1_7`, `fuseZ_2_0`, `fuseZ_3_0`, `fuseZ_3_1`, `fuseZ_3_2`, `fuseZ_3_4`, `fuseZ_3_5`, `fuseZ_3_6`, `fuseZ_3_7`, `fuseZ_4_3`, `fuseZ_4_4`, `fuseZ_4_5`, `fuseZ_4_6`, `fuseZ_4_7`, `fuseZ_5_0`. -/

/-! ### The triple `(3,1,3)`

`gaugeSizeL = gaugeSizeR = (4,4)`, `dim D_7 = 2`, certgen parity `1`; the transported connector literal. -/
section Triple_3_1_3
open Module
theorem hsz3_1_3 : realGauge.gaugeSizeR 3 1 3 = realGauge.gaugeSizeL 3 1 3 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`8 x 8 x 2`). -/
def TL3_1_3 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]]]

/-- The same literal read at the composite frame `Fin 4 ⊕ Fin 4`. -/
noncomputable def Tc3_1_3 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet TL3_1_3 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_7`. -/
noncomputable def T3_1_3 : ((realGauge.D ((3 : ZMod 8) + 1 + 3)).matrixSuper
    (realGauge.gaugeSizeL 3 1 3).1 (realGauge.gaugeSizeL 3 1 3).2).carrier :=
  matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Tc3_1_3

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT3_1_3 : T3_1_3 ∈ ((realGauge.D ((3 : ZMod 8) + 1 + 3)).matrixSuper
    (realGauge.gaugeSizeL 3 1 3).1 (realGauge.gaugeSizeL 3 1 3).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((3 : ZMod 8) + 1 + 3) Tc3_1_3 1 (by decide)

theorem T3_1_3_ne_zero : T3_1_3 ≠ 0 :=
  matOfCoeff_ne_zero ((3 : ZMod 8) + 1 + 3) Tc3_1_3 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨1, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa3_1_3_0 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I)
          * realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 3) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya3_1_3_0 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((3 : ZMod 8) + 1) (3 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa3_1_3_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa3_1_3_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xca3_1_3_0 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_3_0 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_3_0 : ∀ I J g, Xa3_1_3_0 I J g = Xca3_1_3_0 I J g := by
  decide +kernel

theorem hYtaba3_1_3_0 : ∀ I J g, Ya3_1_3_0 I J g = Yca3_1_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta3_1_3_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xa3_1_3_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 hfuseZ_3_4 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xca3_1_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Ya3_1_3_0 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hfuseZ_3_1 hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Yca3_1_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 3) (realGauge.gaugeSizeL 3 1 3).1 (realGauge.gaugeSizeL 3 1 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_3_0 TL3_1_3 YLa3_1_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa3_1_3_1 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I)
          * realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 3) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 3) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya3_1_3_1 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((3 : ZMod 8) + 1) (3 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa3_1_3_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa3_1_3_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca3_1_3_1 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_3_1 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_3_1 : ∀ I J g, Xa3_1_3_1 I J g = Xca3_1_3_1 I J g := by
  decide +kernel

theorem hYtaba3_1_3_1 : ∀ I J g, Ya3_1_3_1 I J g = Yca3_1_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `-1`). -/
theorem hinta3_1_3_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xa3_1_3_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 hfuseZ_3_4 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xca3_1_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Ya3_1_3_1 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hfuseZ_3_1 hfuseZ_4_3 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Yca3_1_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 3) (realGauge.gaugeSizeL 3 1 3).1 (realGauge.gaugeSizeL 3 1 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_3_1 TL3_1_3 YLa3_1_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa3_1_3_2 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I)
          * realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 3) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 3) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya3_1_3_2 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((3 : ZMod 8) + 1) (3 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa3_1_3_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa3_1_3_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]]]

noncomputable def Xca3_1_3_2 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_3_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_3_2 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_3_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_3_2 : ∀ I J g, Xa3_1_3_2 I J g = Xca3_1_3_2 I J g := by
  decide +kernel

theorem hYtaba3_1_3_2 : ∀ I J g, Ya3_1_3_2 I J g = Yca3_1_3_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `-1`). -/
theorem hinta3_1_3_2 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xa3_1_3_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 hfuseZ_3_4 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xca3_1_3_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_3_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Ya3_1_3_2 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hfuseZ_3_1 hfuseZ_4_3 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Yca3_1_3_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_3_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 3) (realGauge.gaugeSizeL 3 1 3).1 (realGauge.gaugeSizeL 3 1 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_3_2 TL3_1_3 YLa3_1_3_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa3_1_3_3 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I)
          * realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 3) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 3) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya3_1_3_3 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((3 : ZMod 8) + 1) (3 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa3_1_3_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa3_1_3_3 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]]]

noncomputable def Xca3_1_3_3 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_3_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_3_3 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_3_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_3_3 : ∀ I J g, Xa3_1_3_3 I J g = Xca3_1_3_3 I J g := by
  decide +kernel

theorem hYtaba3_1_3_3 : ∀ I J g, Ya3_1_3_3 I J g = Yca3_1_3_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta3_1_3_3 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xa3_1_3_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 hfuseZ_3_4 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xca3_1_3_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_3_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Ya3_1_3_3 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hfuseZ_3_1 hfuseZ_4_3 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Yca3_1_3_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_3_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 3) (realGauge.gaugeSizeL 3 1 3).1 (realGauge.gaugeSizeL 3 1 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_3_3 TL3_1_3 YLa3_1_3_3 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Xa3_1_3_4 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I)
          * realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 3) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 3) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Ya3_1_3_4 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((3 : ZMod 8) + 1) (3 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `4`, pre-tabulated. -/
def XLa3_1_3_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `4`, pre-tabulated. -/
def YLa3_1_3_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca3_1_3_4 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_3_4 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_3_4 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_3_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_3_4 : ∀ I J g, Xa3_1_3_4 I J g = Xca3_1_3_4 I J g := by
  decide +kernel

theorem hYtaba3_1_3_4 : ∀ I J g, Ya3_1_3_4 I J g = Yca3_1_3_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `4`** (Koszul sign `-1`). -/
theorem hinta3_1_3_4 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xa3_1_3_4 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 hfuseZ_3_4 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xca3_1_3_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_3_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Ya3_1_3_4 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hfuseZ_3_1 hfuseZ_4_3 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Yca3_1_3_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_3_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 3) (realGauge.gaugeSizeL 3 1 3).1 (realGauge.gaugeSizeL 3 1 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_3_4 TL3_1_3 YLa3_1_3_4 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Xa3_1_3_5 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I)
          * realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 3) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 3) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Ya3_1_3_5 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((3 : ZMod 8) + 1) (3 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `5`, pre-tabulated. -/
def XLa3_1_3_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `5`, pre-tabulated. -/
def YLa3_1_3_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca3_1_3_5 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_3_5 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_3_5 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_3_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_3_5 : ∀ I J g, Xa3_1_3_5 I J g = Xca3_1_3_5 I J g := by
  decide +kernel

theorem hYtaba3_1_3_5 : ∀ I J g, Ya3_1_3_5 I J g = Yca3_1_3_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `5`** (Koszul sign `+1`). -/
theorem hinta3_1_3_5 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xa3_1_3_5 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 hfuseZ_3_4 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xca3_1_3_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_3_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Ya3_1_3_5 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hfuseZ_3_1 hfuseZ_4_3 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Yca3_1_3_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_3_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 3) (realGauge.gaugeSizeL 3 1 3).1 (realGauge.gaugeSizeL 3 1 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_3_5 TL3_1_3 YLa3_1_3_5 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Xa3_1_3_6 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I)
          * realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 3) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 3) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Ya3_1_3_6 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((3 : ZMod 8) + 1) (3 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `6`, pre-tabulated. -/
def XLa3_1_3_6 : List (List (List ℤ)) :=
  [[[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `6`, pre-tabulated. -/
def YLa3_1_3_6 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca3_1_3_6 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_3_6 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_3_6 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_3_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_3_6 : ∀ I J g, Xa3_1_3_6 I J g = Xca3_1_3_6 I J g := by
  decide +kernel

theorem hYtaba3_1_3_6 : ∀ I J g, Ya3_1_3_6 I J g = Yca3_1_3_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `6`** (Koszul sign `+1`). -/
theorem hinta3_1_3_6 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xa3_1_3_6 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 hfuseZ_3_4 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xca3_1_3_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_3_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Ya3_1_3_6 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hfuseZ_3_1 hfuseZ_4_3 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Yca3_1_3_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_3_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 3) (realGauge.gaugeSizeL 3 1 3).1 (realGauge.gaugeSizeL 3 1 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_3_6 TL3_1_3 YLa3_1_3_6 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Xa3_1_3_7 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I)
          * realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 3) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 3) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Ya3_1_3_7 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((3 : ZMod 8) + 1) (3 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `7`, pre-tabulated. -/
def XLa3_1_3_7 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]]]

/-- Left route at the `a`-slot generator `7`, pre-tabulated. -/
def YLa3_1_3_7 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca3_1_3_7 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_3_7 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_3_7 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_3_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_3_7 : ∀ I J g, Xa3_1_3_7 I J g = Xca3_1_3_7 I J g := by
  decide +kernel

theorem hYtaba3_1_3_7 : ∀ I J g, Ya3_1_3_7 I J g = Yca3_1_3_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `7`** (Koszul sign `-1`). -/
theorem hinta3_1_3_7 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xa3_1_3_7 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 hfuseZ_3_4 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xca3_1_3_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_3_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Ya3_1_3_7 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hfuseZ_3_1 hfuseZ_4_3 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Yca3_1_3_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_3_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 3) (realGauge.gaugeSizeL 3 1 3).1 (realGauge.gaugeSizeL 3 1 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_3_7 TL3_1_3 YLa3_1_3_7 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb3_1_3_0 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 3) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb3_1_3_0 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((3 : ZMod 8) + 1) (3 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb3_1_3_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb3_1_3_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcb3_1_3_0 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb3_1_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_1_3_0 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb3_1_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_1_3_0 : ∀ I J g, Xb3_1_3_0 I J g = Xcb3_1_3_0 I J g := by
  decide +kernel

theorem hYtabb3_1_3_0 : ∀ I J g, Yb3_1_3_0 I J g = Ycb3_1_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb3_1_3_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T3_1_3
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xb3_1_3_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 hfuseZ_1_3 hfuseZ_3_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xcb3_1_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_1_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Yb3_1_3_0 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hfuseZ_3_1 hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Ycb3_1_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_1_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 3) (realGauge.gaugeSizeL 3 1 3).1 (realGauge.gaugeSizeL 3 1 3).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb3_1_3_0 TL3_1_3 YLb3_1_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb3_1_3_1 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 3) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb3_1_3_1 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((3 : ZMod 8) + 1) (3 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb3_1_3_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb3_1_3_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb3_1_3_1 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb3_1_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_1_3_1 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb3_1_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_1_3_1 : ∀ I J g, Xb3_1_3_1 I J g = Xcb3_1_3_1 I J g := by
  decide +kernel

theorem hYtabb3_1_3_1 : ∀ I J g, Yb3_1_3_1 I J g = Ycb3_1_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintb3_1_3_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T3_1_3
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xb3_1_3_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 hfuseZ_1_3 hfuseZ_3_4 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xcb3_1_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_1_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Yb3_1_3_1 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hfuseZ_3_1 hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Ycb3_1_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_1_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 3) (realGauge.gaugeSizeL 3 1 3).1 (realGauge.gaugeSizeL 3 1 3).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb3_1_3_1 TL3_1_3 YLb3_1_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc3_1_3_0 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 3) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc3_1_3_0 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) = (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow ((3 : ZMod 8) + 1) (3 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc3_1_3_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc3_1_3_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcc3_1_3_0 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc3_1_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_1_3_0 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc3_1_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_1_3_0 : ∀ I J g, Xc3_1_3_0 I J g = Xcc3_1_3_0 I J g := by
  decide +kernel

theorem hYtabc3_1_3_0 : ∀ I J g, Yc3_1_3_0 I J g = Ycc3_1_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc3_1_3_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xc3_1_3_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 hfuseZ_1_3 hfuseZ_3_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xcc3_1_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_1_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Yc3_1_3_0 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Ycc3_1_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_1_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 3) (realGauge.gaugeSizeL 3 1 3).1 (realGauge.gaugeSizeL 3 1 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_1_3_0 TL3_1_3 YLc3_1_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc3_1_3_1 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 3) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc3_1_3_1 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) = (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow ((3 : ZMod 8) + 1) (3 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc3_1_3_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc3_1_3_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]]]

noncomputable def Xcc3_1_3_1 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc3_1_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_1_3_1 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc3_1_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_1_3_1 : ∀ I J g, Xc3_1_3_1 I J g = Xcc3_1_3_1 I J g := by
  decide +kernel

theorem hYtabc3_1_3_1 : ∀ I J g, Yc3_1_3_1 I J g = Ycc3_1_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintc3_1_3_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xc3_1_3_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 hfuseZ_1_3 hfuseZ_3_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xcc3_1_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_1_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Yc3_1_3_1 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Ycc3_1_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_1_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 3) (realGauge.gaugeSizeL 3 1 3).1 (realGauge.gaugeSizeL 3 1 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_1_3_1 TL3_1_3 YLc3_1_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc3_1_3_2 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 3) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc3_1_3_2 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) = (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow ((3 : ZMod 8) + 1) (3 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc3_1_3_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc3_1_3_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc3_1_3_2 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc3_1_3_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_1_3_2 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc3_1_3_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_1_3_2 : ∀ I J g, Xc3_1_3_2 I J g = Xcc3_1_3_2 I J g := by
  decide +kernel

theorem hYtabc3_1_3_2 : ∀ I J g, Yc3_1_3_2 I J g = Ycc3_1_3_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintc3_1_3_2 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xc3_1_3_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 hfuseZ_1_3 hfuseZ_3_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xcc3_1_3_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_1_3_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Yc3_1_3_2 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Ycc3_1_3_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_1_3_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 3) (realGauge.gaugeSizeL 3 1 3).1 (realGauge.gaugeSizeL 3 1 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_1_3_2 TL3_1_3 YLc3_1_3_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc3_1_3_3 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 3) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc3_1_3_3 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) = (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow ((3 : ZMod 8) + 1) (3 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc3_1_3_3 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc3_1_3_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc3_1_3_3 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc3_1_3_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_1_3_3 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc3_1_3_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_1_3_3 : ∀ I J g, Xc3_1_3_3 I J g = Xcc3_1_3_3 I J g := by
  decide +kernel

theorem hYtabc3_1_3_3 : ∀ I J g, Yc3_1_3_3 I J g = Ycc3_1_3_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc3_1_3_3 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xc3_1_3_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 hfuseZ_1_3 hfuseZ_3_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xcc3_1_3_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_1_3_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Yc3_1_3_3 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Ycc3_1_3_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_1_3_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 3) (realGauge.gaugeSizeL 3 1 3).1 (realGauge.gaugeSizeL 3 1 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_1_3_3 TL3_1_3 YLc3_1_3_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Xc3_1_3_4 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 3) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Yc3_1_3_4 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) = (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow ((3 : ZMod 8) + 1) (3 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `4`, pre-tabulated. -/
def XLc3_1_3_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `4`, pre-tabulated. -/
def YLc3_1_3_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc3_1_3_4 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc3_1_3_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_1_3_4 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc3_1_3_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_1_3_4 : ∀ I J g, Xc3_1_3_4 I J g = Xcc3_1_3_4 I J g := by
  decide +kernel

theorem hYtabc3_1_3_4 : ∀ I J g, Yc3_1_3_4 I J g = Ycc3_1_3_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `4`** (Koszul sign `-1`). -/
theorem hintc3_1_3_4 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xc3_1_3_4 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 hfuseZ_1_3 hfuseZ_3_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xcc3_1_3_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_1_3_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Yc3_1_3_4 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Ycc3_1_3_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_1_3_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 3) (realGauge.gaugeSizeL 3 1 3).1 (realGauge.gaugeSizeL 3 1 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_1_3_4 TL3_1_3 YLc3_1_3_4 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Xc3_1_3_5 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 3) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Yc3_1_3_5 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) = (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow ((3 : ZMod 8) + 1) (3 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `5`, pre-tabulated. -/
def XLc3_1_3_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `5`, pre-tabulated. -/
def YLc3_1_3_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc3_1_3_5 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc3_1_3_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_1_3_5 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc3_1_3_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_1_3_5 : ∀ I J g, Xc3_1_3_5 I J g = Xcc3_1_3_5 I J g := by
  decide +kernel

theorem hYtabc3_1_3_5 : ∀ I J g, Yc3_1_3_5 I J g = Ycc3_1_3_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintc3_1_3_5 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xc3_1_3_5 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 hfuseZ_1_3 hfuseZ_3_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xcc3_1_3_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_1_3_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Yc3_1_3_5 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Ycc3_1_3_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_1_3_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 3) (realGauge.gaugeSizeL 3 1 3).1 (realGauge.gaugeSizeL 3 1 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_1_3_5 TL3_1_3 YLc3_1_3_5 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Xc3_1_3_6 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 3) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Yc3_1_3_6 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) = (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow ((3 : ZMod 8) + 1) (3 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `6`, pre-tabulated. -/
def XLc3_1_3_6 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `6`, pre-tabulated. -/
def YLc3_1_3_6 : List (List (List ℤ)) :=
  [[[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]]]

noncomputable def Xcc3_1_3_6 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc3_1_3_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_1_3_6 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc3_1_3_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_1_3_6 : ∀ I J g, Xc3_1_3_6 I J g = Xcc3_1_3_6 I J g := by
  decide +kernel

theorem hYtabc3_1_3_6 : ∀ I J g, Yc3_1_3_6 I J g = Ycc3_1_3_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintc3_1_3_6 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xc3_1_3_6 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 hfuseZ_1_3 hfuseZ_3_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xcc3_1_3_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_1_3_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Yc3_1_3_6 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Ycc3_1_3_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_1_3_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 3) (realGauge.gaugeSizeL 3 1 3).1 (realGauge.gaugeSizeL 3 1 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_1_3_6 TL3_1_3 YLc3_1_3_6 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Xc3_1_3_7 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ro (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 3) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 I) (ri (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Yc3_1_3_7 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) = (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (lo (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow ((3 : ZMod 8) + 1) (3 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `7`, pre-tabulated. -/
def XLc3_1_3_7 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `7`, pre-tabulated. -/
def YLc3_1_3_7 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]]]

noncomputable def Xcc3_1_3_7 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc3_1_3_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_1_3_7 : (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc3_1_3_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_1_3_7 : ∀ I J g, Xc3_1_3_7 I J g = Xcc3_1_3_7 I J g := by
  decide +kernel

theorem hYtabc3_1_3_7 : ∀ I J g, Yc3_1_3_7 I J g = Ycc3_1_3_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `7`** (Koszul sign `-1`). -/
theorem hintc3_1_3_7 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xc3_1_3_7 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 hfuseZ_1_3 hfuseZ_3_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Xcc3_1_3_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_1_3_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Yc3_1_3_7 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 3)) Ycc3_1_3_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 3).2)) (realRepBasis ((3 : ZMod 8) + 1 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_1_3_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 3) (realGauge.gaugeSizeL 3 1 3).1 (realGauge.gaugeSizeL 3 1 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_1_3_7 TL3_1_3 YLc3_1_3_7 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint3_1_3 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T3_1_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T3_1_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hinta3_1_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hinta3_1_3_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hinta3_1_3_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hinta3_1_3_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hinta3_1_3_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hinta3_1_3_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hinta3_1_3_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hinta3_1_3_7

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint3_1_3 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T3_1_3
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T3_1_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hintb3_1_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hintb3_1_3_1

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint3_1_3 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T3_1_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T3_1_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hintc3_1_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hintc3_1_3_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hintc3_1_3_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hintc3_1_3_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hintc3_1_3_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hintc3_1_3_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hintc3_1_3_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hintc3_1_3_7

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT3_1_3_mem_gInterSpace :
    gtOfT ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 T3_1_3 ∈ gInterSpace ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 hT3_1_3 hAint3_1_3 hBint3_1_3 hCint3_1_3

theorem gtOfT3_1_3_ne_zero : gtOfT ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 T3_1_3 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) hsz3_1_3 T3_1_3_ne_zero

theorem gInterSpace3_1_3_ne_bot : gInterSpace ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT3_1_3_mem_gInterSpace, gtOfT3_1_3_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_3_1_3 : gParity ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (3 : ZMod 8) gInterSpace3_1_3_ne_bot).symm

end Triple_3_1_3

/-! ### The triple `(3,1,4)`

`gaugeSizeL = gaugeSizeR = (4,4)`, `dim D_0 = 1`, certgen parity `1`; the transported connector literal. -/
section Triple_3_1_4
open Module
theorem hsz3_1_4 : realGauge.gaugeSizeR 3 1 4 = realGauge.gaugeSizeL 3 1 4 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`8 x 8 x 1`). -/
def TL3_1_4 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [1], [-1], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [1], [1], [0]],
   [[-1], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [-1], [-1], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [1], [-1], [0], [0], [0], [0], [0]]]

/-- The same literal read at the composite frame `Fin 4 ⊕ Fin 4`. -/
noncomputable def Tc3_1_4 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet TL3_1_4 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_0`. -/
noncomputable def T3_1_4 : ((realGauge.D ((3 : ZMod 8) + 1 + 4)).matrixSuper
    (realGauge.gaugeSizeL 3 1 4).1 (realGauge.gaugeSizeL 3 1 4).2).carrier :=
  matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Tc3_1_4

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT3_1_4 : T3_1_4 ∈ ((realGauge.D ((3 : ZMod 8) + 1 + 4)).matrixSuper
    (realGauge.gaugeSizeL 3 1 4).1 (realGauge.gaugeSizeL 3 1 4).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((3 : ZMod 8) + 1 + 4) Tc3_1_4 1 (by decide)

theorem T3_1_4_ne_zero : T3_1_4 ≠ 0 :=
  matOfCoeff_ne_zero ((3 : ZMod 8) + 1 + 4) Tc3_1_4 (Sum.inl ⟨0, by decide⟩) (Sum.inr ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa3_1_4_0 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (4 : ZMod 8)).1 (realSize (1 : ZMod 8) (4 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I)
          * realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 4) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya3_1_4_0 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((3 : ZMod 8) + 1) (4 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa3_1_4_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa3_1_4_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xca3_1_4_0 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_4_0 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_4_0 : ∀ I J g, Xa3_1_4_0 I J g = Xca3_1_4_0 I J g := by
  decide +kernel

theorem hYtaba3_1_4_0 : ∀ I J g, Ya3_1_4_0 I J g = Yca3_1_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta3_1_4_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xa3_1_4_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 hfuseZ_3_5 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xca3_1_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Ya3_1_4_0 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hfuseZ_3_1 hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Yca3_1_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 4) (realGauge.gaugeSizeL 3 1 4).1 (realGauge.gaugeSizeL 3 1 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_4_0 TL3_1_4 YLa3_1_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa3_1_4_1 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (4 : ZMod 8)).1 (realSize (1 : ZMod 8) (4 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I)
          * realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 4) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 4) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya3_1_4_1 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((3 : ZMod 8) + 1) (4 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa3_1_4_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa3_1_4_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xca3_1_4_1 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_4_1 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_4_1 : ∀ I J g, Xa3_1_4_1 I J g = Xca3_1_4_1 I J g := by
  decide +kernel

theorem hYtaba3_1_4_1 : ∀ I J g, Ya3_1_4_1 I J g = Yca3_1_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `-1`). -/
theorem hinta3_1_4_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xa3_1_4_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 hfuseZ_3_5 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xca3_1_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Ya3_1_4_1 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hfuseZ_3_1 hfuseZ_4_4 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Yca3_1_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 4) (realGauge.gaugeSizeL 3 1 4).1 (realGauge.gaugeSizeL 3 1 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_4_1 TL3_1_4 YLa3_1_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa3_1_4_2 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (4 : ZMod 8)).1 (realSize (1 : ZMod 8) (4 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I)
          * realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 4) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 4) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya3_1_4_2 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((3 : ZMod 8) + 1) (4 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa3_1_4_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa3_1_4_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]]]

noncomputable def Xca3_1_4_2 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_4_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_4_2 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_4_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_4_2 : ∀ I J g, Xa3_1_4_2 I J g = Xca3_1_4_2 I J g := by
  decide +kernel

theorem hYtaba3_1_4_2 : ∀ I J g, Ya3_1_4_2 I J g = Yca3_1_4_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `-1`). -/
theorem hinta3_1_4_2 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xa3_1_4_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 hfuseZ_3_5 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xca3_1_4_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_4_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Ya3_1_4_2 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hfuseZ_3_1 hfuseZ_4_4 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Yca3_1_4_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_4_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 4) (realGauge.gaugeSizeL 3 1 4).1 (realGauge.gaugeSizeL 3 1 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_4_2 TL3_1_4 YLa3_1_4_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa3_1_4_3 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (4 : ZMod 8)).1 (realSize (1 : ZMod 8) (4 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I)
          * realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 4) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 4) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya3_1_4_3 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((3 : ZMod 8) + 1) (4 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa3_1_4_3 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa3_1_4_3 : List (List (List ℤ)) :=
  [[[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]]]

noncomputable def Xca3_1_4_3 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_4_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_4_3 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_4_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_4_3 : ∀ I J g, Xa3_1_4_3 I J g = Xca3_1_4_3 I J g := by
  decide +kernel

theorem hYtaba3_1_4_3 : ∀ I J g, Ya3_1_4_3 I J g = Yca3_1_4_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta3_1_4_3 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xa3_1_4_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 hfuseZ_3_5 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xca3_1_4_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_4_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Ya3_1_4_3 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hfuseZ_3_1 hfuseZ_4_4 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Yca3_1_4_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_4_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 4) (realGauge.gaugeSizeL 3 1 4).1 (realGauge.gaugeSizeL 3 1 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_4_3 TL3_1_4 YLa3_1_4_3 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Xa3_1_4_4 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (4 : ZMod 8)).1 (realSize (1 : ZMod 8) (4 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I)
          * realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 4) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 4) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Ya3_1_4_4 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((3 : ZMod 8) + 1) (4 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `4`, pre-tabulated. -/
def XLa3_1_4_4 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `4`, pre-tabulated. -/
def YLa3_1_4_4 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]]]

noncomputable def Xca3_1_4_4 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_4_4 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_4_4 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_4_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_4_4 : ∀ I J g, Xa3_1_4_4 I J g = Xca3_1_4_4 I J g := by
  decide +kernel

theorem hYtaba3_1_4_4 : ∀ I J g, Ya3_1_4_4 I J g = Yca3_1_4_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `4`** (Koszul sign `-1`). -/
theorem hinta3_1_4_4 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xa3_1_4_4 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 hfuseZ_3_5 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xca3_1_4_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_4_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Ya3_1_4_4 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hfuseZ_3_1 hfuseZ_4_4 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Yca3_1_4_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_4_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 4) (realGauge.gaugeSizeL 3 1 4).1 (realGauge.gaugeSizeL 3 1 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_4_4 TL3_1_4 YLa3_1_4_4 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Xa3_1_4_5 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (4 : ZMod 8)).1 (realSize (1 : ZMod 8) (4 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I)
          * realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 4) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 4) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Ya3_1_4_5 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((3 : ZMod 8) + 1) (4 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `5`, pre-tabulated. -/
def XLa3_1_4_5 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]]]

/-- Left route at the `a`-slot generator `5`, pre-tabulated. -/
def YLa3_1_4_5 : List (List (List ℤ)) :=
  [[[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

noncomputable def Xca3_1_4_5 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_4_5 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_4_5 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_4_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_4_5 : ∀ I J g, Xa3_1_4_5 I J g = Xca3_1_4_5 I J g := by
  decide +kernel

theorem hYtaba3_1_4_5 : ∀ I J g, Ya3_1_4_5 I J g = Yca3_1_4_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `5`** (Koszul sign `+1`). -/
theorem hinta3_1_4_5 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xa3_1_4_5 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 hfuseZ_3_5 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xca3_1_4_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_4_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Ya3_1_4_5 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hfuseZ_3_1 hfuseZ_4_4 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Yca3_1_4_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_4_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 4) (realGauge.gaugeSizeL 3 1 4).1 (realGauge.gaugeSizeL 3 1 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_4_5 TL3_1_4 YLa3_1_4_5 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Xa3_1_4_6 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (4 : ZMod 8)).1 (realSize (1 : ZMod 8) (4 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I)
          * realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 4) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 4) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Ya3_1_4_6 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((3 : ZMod 8) + 1) (4 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `6`, pre-tabulated. -/
def XLa3_1_4_6 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `6`, pre-tabulated. -/
def YLa3_1_4_6 : List (List (List ℤ)) :=
  [[[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

noncomputable def Xca3_1_4_6 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_4_6 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_4_6 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_4_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_4_6 : ∀ I J g, Xa3_1_4_6 I J g = Xca3_1_4_6 I J g := by
  decide +kernel

theorem hYtaba3_1_4_6 : ∀ I J g, Ya3_1_4_6 I J g = Yca3_1_4_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `6`** (Koszul sign `+1`). -/
theorem hinta3_1_4_6 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xa3_1_4_6 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 hfuseZ_3_5 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xca3_1_4_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_4_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Ya3_1_4_6 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hfuseZ_3_1 hfuseZ_4_4 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Yca3_1_4_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_4_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 4) (realGauge.gaugeSizeL 3 1 4).1 (realGauge.gaugeSizeL 3 1 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_4_6 TL3_1_4 YLa3_1_4_6 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Xa3_1_4_7 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (4 : ZMod 8)).1 (realSize (1 : ZMod 8) (4 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I)
          * realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 4) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 4) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Ya3_1_4_7 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((3 : ZMod 8) + 1) (4 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `7`, pre-tabulated. -/
def XLa3_1_4_7 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `7`, pre-tabulated. -/
def YLa3_1_4_7 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xca3_1_4_7 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_4_7 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_4_7 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_4_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_4_7 : ∀ I J g, Xa3_1_4_7 I J g = Xca3_1_4_7 I J g := by
  decide +kernel

theorem hYtaba3_1_4_7 : ∀ I J g, Ya3_1_4_7 I J g = Yca3_1_4_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `7`** (Koszul sign `-1`). -/
theorem hinta3_1_4_7 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xa3_1_4_7 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 hfuseZ_3_5 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xca3_1_4_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_4_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Ya3_1_4_7 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hfuseZ_3_1 hfuseZ_4_4 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Yca3_1_4_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_4_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 4) (realGauge.gaugeSizeL 3 1 4).1 (realGauge.gaugeSizeL 3 1 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_4_7 TL3_1_4 YLa3_1_4_7 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb3_1_4_0 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 4) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb3_1_4_0 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((3 : ZMod 8) + 1) (4 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb3_1_4_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb3_1_4_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xcb3_1_4_0 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb3_1_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_1_4_0 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb3_1_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_1_4_0 : ∀ I J g, Xb3_1_4_0 I J g = Xcb3_1_4_0 I J g := by
  decide +kernel

theorem hYtabb3_1_4_0 : ∀ I J g, Yb3_1_4_0 I J g = Ycb3_1_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb3_1_4_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T3_1_4
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xb3_1_4_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 hfuseZ_1_4 hfuseZ_3_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xcb3_1_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_1_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Yb3_1_4_0 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hfuseZ_3_1 hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Ycb3_1_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_1_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 4) (realGauge.gaugeSizeL 3 1 4).1 (realGauge.gaugeSizeL 3 1 4).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb3_1_4_0 TL3_1_4 YLb3_1_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb3_1_4_1 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 4) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb3_1_4_1 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((3 : ZMod 8) + 1) (4 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb3_1_4_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb3_1_4_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xcb3_1_4_1 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb3_1_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_1_4_1 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb3_1_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_1_4_1 : ∀ I J g, Xb3_1_4_1 I J g = Xcb3_1_4_1 I J g := by
  decide +kernel

theorem hYtabb3_1_4_1 : ∀ I J g, Yb3_1_4_1 I J g = Ycb3_1_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintb3_1_4_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T3_1_4
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xb3_1_4_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 hfuseZ_1_4 hfuseZ_3_5 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xcb3_1_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_1_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Yb3_1_4_1 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hfuseZ_3_1 hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Ycb3_1_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_1_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 4) (realGauge.gaugeSizeL 3 1 4).1 (realGauge.gaugeSizeL 3 1 4).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb3_1_4_1 TL3_1_4 YLb3_1_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc3_1_4_0 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 4) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc3_1_4_0 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) = (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_4 (fuseRow ((3 : ZMod 8) + 1) (4 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc3_1_4_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc3_1_4_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xcc3_1_4_0 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc3_1_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_1_4_0 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc3_1_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_1_4_0 : ∀ I J g, Xc3_1_4_0 I J g = Xcc3_1_4_0 I J g := by
  decide +kernel

theorem hYtabc3_1_4_0 : ∀ I J g, Yc3_1_4_0 I J g = Ycc3_1_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc3_1_4_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T3_1_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xc3_1_4_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 hfuseZ_1_4 hfuseZ_3_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xcc3_1_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_1_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Yc3_1_4_0 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Ycc3_1_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_1_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 4) (realGauge.gaugeSizeL 3 1 4).1 (realGauge.gaugeSizeL 3 1 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_1_4_0 TL3_1_4 YLc3_1_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc3_1_4_1 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 4) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc3_1_4_1 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) = (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_4 (fuseRow ((3 : ZMod 8) + 1) (4 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc3_1_4_1 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc3_1_4_1 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]]]

noncomputable def Xcc3_1_4_1 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc3_1_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_1_4_1 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc3_1_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_1_4_1 : ∀ I J g, Xc3_1_4_1 I J g = Xcc3_1_4_1 I J g := by
  decide +kernel

theorem hYtabc3_1_4_1 : ∀ I J g, Yc3_1_4_1 I J g = Ycc3_1_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc3_1_4_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T3_1_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xc3_1_4_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 hfuseZ_1_4 hfuseZ_3_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xcc3_1_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_1_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Yc3_1_4_1 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Ycc3_1_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_1_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 4) (realGauge.gaugeSizeL 3 1 4).1 (realGauge.gaugeSizeL 3 1 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_1_4_1 TL3_1_4 YLc3_1_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc3_1_4_2 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 4) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc3_1_4_2 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) = (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_4 (fuseRow ((3 : ZMod 8) + 1) (4 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc3_1_4_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc3_1_4_2 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]]]

noncomputable def Xcc3_1_4_2 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc3_1_4_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_1_4_2 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc3_1_4_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_1_4_2 : ∀ I J g, Xc3_1_4_2 I J g = Xcc3_1_4_2 I J g := by
  decide +kernel

theorem hYtabc3_1_4_2 : ∀ I J g, Yc3_1_4_2 I J g = Ycc3_1_4_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc3_1_4_2 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T3_1_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xc3_1_4_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 hfuseZ_1_4 hfuseZ_3_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xcc3_1_4_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_1_4_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Yc3_1_4_2 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Ycc3_1_4_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_1_4_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 4) (realGauge.gaugeSizeL 3 1 4).1 (realGauge.gaugeSizeL 3 1 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_1_4_2 TL3_1_4 YLc3_1_4_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc3_1_4_3 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) (ro (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 4) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 I) (ri (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc3_1_4_3 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) = (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (lo (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_4 (fuseRow ((3 : ZMod 8) + 1) (4 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc3_1_4_3 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc3_1_4_3 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

noncomputable def Xcc3_1_4_3 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc3_1_4_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_1_4_3 : (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc3_1_4_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_1_4_3 : ∀ I J g, Xc3_1_4_3 I J g = Xcc3_1_4_3 I J g := by
  decide +kernel

theorem hYtabc3_1_4_3 : ∀ I J g, Yc3_1_4_3 I J g = Ycc3_1_4_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc3_1_4_3 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T3_1_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xc3_1_4_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 hfuseZ_1_4 hfuseZ_3_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Xcc3_1_4_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_1_4_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Yc3_1_4_3 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 4)) Ycc3_1_4_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 4).2)) (realRepBasis ((3 : ZMod 8) + 1 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_1_4_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 4) (realGauge.gaugeSizeL 3 1 4).1 (realGauge.gaugeSizeL 3 1 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_1_4_3 TL3_1_4 YLc3_1_4_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint3_1_4 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T3_1_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T3_1_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hinta3_1_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hinta3_1_4_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hinta3_1_4_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hinta3_1_4_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hinta3_1_4_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hinta3_1_4_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hinta3_1_4_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hinta3_1_4_7

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint3_1_4 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T3_1_4
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T3_1_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hintb3_1_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hintb3_1_4_1

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint3_1_4 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T3_1_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T3_1_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hintc3_1_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hintc3_1_4_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hintc3_1_4_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hintc3_1_4_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT3_1_4_mem_gInterSpace :
    gtOfT ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 T3_1_4 ∈ gInterSpace ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 hT3_1_4 hAint3_1_4 hBint3_1_4 hCint3_1_4

theorem gtOfT3_1_4_ne_zero : gtOfT ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 T3_1_4 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) hsz3_1_4 T3_1_4_ne_zero

theorem gInterSpace3_1_4_ne_bot : gInterSpace ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT3_1_4_mem_gInterSpace, gtOfT3_1_4_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_3_1_4 : gParity ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (4 : ZMod 8) gInterSpace3_1_4_ne_bot).symm

end Triple_3_1_4

/-! ### The triple `(3,1,5)`

`gaugeSizeL = gaugeSizeR = (4,4)`, `dim D_1 = 2`, certgen parity `1`; the transported connector literal. -/
section Triple_3_1_5
open Module
theorem hsz3_1_5 : realGauge.gaugeSizeR 3 1 5 = realGauge.gaugeSizeL 3 1 5 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`8 x 8 x 2`). -/
def TL3_1_5 : List (List (List ℤ)) :=
  [[[0, -1], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, -1]],
   [[-1, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- The same literal read at the composite frame `Fin 4 ⊕ Fin 4`. -/
noncomputable def Tc3_1_5 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet TL3_1_5 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_1`. -/
noncomputable def T3_1_5 : ((realGauge.D ((3 : ZMod 8) + 1 + 5)).matrixSuper
    (realGauge.gaugeSizeL 3 1 5).1 (realGauge.gaugeSizeL 3 1 5).2).carrier :=
  matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Tc3_1_5

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT3_1_5 : T3_1_5 ∈ ((realGauge.D ((3 : ZMod 8) + 1 + 5)).matrixSuper
    (realGauge.gaugeSizeL 3 1 5).1 (realGauge.gaugeSizeL 3 1 5).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((3 : ZMod 8) + 1 + 5) Tc3_1_5 1 (by decide)

theorem T3_1_5_ne_zero : T3_1_5 ≠ 0 :=
  matOfCoeff_ne_zero ((3 : ZMod 8) + 1 + 5) Tc3_1_5 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨1, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa3_1_5_0 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (5 : ZMod 8)).1 (realSize (1 : ZMod 8) (5 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I)
          * realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_6 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 5) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya3_1_5_0 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((3 : ZMod 8) + 1) (5 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa3_1_5_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa3_1_5_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xca3_1_5_0 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_5_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_5_0 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_5_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_5_0 : ∀ I J g, Xa3_1_5_0 I J g = Xca3_1_5_0 I J g := by
  decide +kernel

theorem hYtaba3_1_5_0 : ∀ I J g, Ya3_1_5_0 I J g = Yca3_1_5_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta3_1_5_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_5
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_5 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xa3_1_5_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 hfuseZ_3_6 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xca3_1_5_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_5_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Ya3_1_5_0 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_3_1 hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Yca3_1_5_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_5_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 3 1 5).1 (realGauge.gaugeSizeL 3 1 5).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_5_0 TL3_1_5 YLa3_1_5_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa3_1_5_1 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (5 : ZMod 8)).1 (realSize (1 : ZMod 8) (5 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I)
          * realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_6 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 5) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 5) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya3_1_5_1 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((3 : ZMod 8) + 1) (5 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa3_1_5_1 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa3_1_5_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca3_1_5_1 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_5_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_5_1 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_5_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_5_1 : ∀ I J g, Xa3_1_5_1 I J g = Xca3_1_5_1 I J g := by
  decide +kernel

theorem hYtaba3_1_5_1 : ∀ I J g, Ya3_1_5_1 I J g = Yca3_1_5_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `-1`). -/
theorem hinta3_1_5_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_5
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_5 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xa3_1_5_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 hfuseZ_3_6 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xca3_1_5_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_5_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Ya3_1_5_1 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_3_1 hfuseZ_4_5 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Yca3_1_5_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_5_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 3 1 5).1 (realGauge.gaugeSizeL 3 1 5).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_5_1 TL3_1_5 YLa3_1_5_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa3_1_5_2 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (5 : ZMod 8)).1 (realSize (1 : ZMod 8) (5 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I)
          * realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_6 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 5) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 5) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya3_1_5_2 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((3 : ZMod 8) + 1) (5 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa3_1_5_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa3_1_5_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]]]

noncomputable def Xca3_1_5_2 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_5_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_5_2 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_5_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_5_2 : ∀ I J g, Xa3_1_5_2 I J g = Xca3_1_5_2 I J g := by
  decide +kernel

theorem hYtaba3_1_5_2 : ∀ I J g, Ya3_1_5_2 I J g = Yca3_1_5_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `-1`). -/
theorem hinta3_1_5_2 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_5
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_5 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xa3_1_5_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 hfuseZ_3_6 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xca3_1_5_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_5_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Ya3_1_5_2 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_3_1 hfuseZ_4_5 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Yca3_1_5_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_5_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 3 1 5).1 (realGauge.gaugeSizeL 3 1 5).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_5_2 TL3_1_5 YLa3_1_5_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa3_1_5_3 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (5 : ZMod 8)).1 (realSize (1 : ZMod 8) (5 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I)
          * realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_6 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 5) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 5) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya3_1_5_3 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((3 : ZMod 8) + 1) (5 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa3_1_5_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa3_1_5_3 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]]]

noncomputable def Xca3_1_5_3 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_5_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_5_3 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_5_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_5_3 : ∀ I J g, Xa3_1_5_3 I J g = Xca3_1_5_3 I J g := by
  decide +kernel

theorem hYtaba3_1_5_3 : ∀ I J g, Ya3_1_5_3 I J g = Yca3_1_5_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta3_1_5_3 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_5
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_5 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xa3_1_5_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 hfuseZ_3_6 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xca3_1_5_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_5_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Ya3_1_5_3 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_3_1 hfuseZ_4_5 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Yca3_1_5_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_5_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 3 1 5).1 (realGauge.gaugeSizeL 3 1 5).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_5_3 TL3_1_5 YLa3_1_5_3 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Xa3_1_5_4 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (5 : ZMod 8)).1 (realSize (1 : ZMod 8) (5 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I)
          * realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_6 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 5) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 5) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Ya3_1_5_4 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((3 : ZMod 8) + 1) (5 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `4`, pre-tabulated. -/
def XLa3_1_5_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `4`, pre-tabulated. -/
def YLa3_1_5_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca3_1_5_4 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_5_4 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_5_4 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_5_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_5_4 : ∀ I J g, Xa3_1_5_4 I J g = Xca3_1_5_4 I J g := by
  decide +kernel

theorem hYtaba3_1_5_4 : ∀ I J g, Ya3_1_5_4 I J g = Yca3_1_5_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `4`** (Koszul sign `-1`). -/
theorem hinta3_1_5_4 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_5
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_5 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xa3_1_5_4 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 hfuseZ_3_6 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xca3_1_5_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_5_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Ya3_1_5_4 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_3_1 hfuseZ_4_5 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Yca3_1_5_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_5_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 3 1 5).1 (realGauge.gaugeSizeL 3 1 5).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_5_4 TL3_1_5 YLa3_1_5_4 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Xa3_1_5_5 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (5 : ZMod 8)).1 (realSize (1 : ZMod 8) (5 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I)
          * realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_6 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 5) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 5) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Ya3_1_5_5 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((3 : ZMod 8) + 1) (5 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `5`, pre-tabulated. -/
def XLa3_1_5_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `5`, pre-tabulated. -/
def YLa3_1_5_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca3_1_5_5 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_5_5 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_5_5 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_5_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_5_5 : ∀ I J g, Xa3_1_5_5 I J g = Xca3_1_5_5 I J g := by
  decide +kernel

theorem hYtaba3_1_5_5 : ∀ I J g, Ya3_1_5_5 I J g = Yca3_1_5_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `5`** (Koszul sign `+1`). -/
theorem hinta3_1_5_5 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_5
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_5 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xa3_1_5_5 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 hfuseZ_3_6 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xca3_1_5_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_5_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Ya3_1_5_5 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_3_1 hfuseZ_4_5 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Yca3_1_5_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_5_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 3 1 5).1 (realGauge.gaugeSizeL 3 1 5).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_5_5 TL3_1_5 YLa3_1_5_5 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Xa3_1_5_6 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (5 : ZMod 8)).1 (realSize (1 : ZMod 8) (5 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I)
          * realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_6 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 5) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 5) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Ya3_1_5_6 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((3 : ZMod 8) + 1) (5 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `6`, pre-tabulated. -/
def XLa3_1_5_6 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `6`, pre-tabulated. -/
def YLa3_1_5_6 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca3_1_5_6 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_5_6 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_5_6 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_5_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_5_6 : ∀ I J g, Xa3_1_5_6 I J g = Xca3_1_5_6 I J g := by
  decide +kernel

theorem hYtaba3_1_5_6 : ∀ I J g, Ya3_1_5_6 I J g = Yca3_1_5_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `6`** (Koszul sign `+1`). -/
theorem hinta3_1_5_6 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_5
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_5 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xa3_1_5_6 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 hfuseZ_3_6 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xca3_1_5_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_5_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Ya3_1_5_6 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_3_1 hfuseZ_4_5 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Yca3_1_5_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_5_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 3 1 5).1 (realGauge.gaugeSizeL 3 1 5).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_5_6 TL3_1_5 YLa3_1_5_6 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Xa3_1_5_7 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (5 : ZMod 8)).1 (realSize (1 : ZMod 8) (5 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I)
          * realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_6 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 5) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 5) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Ya3_1_5_7 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((3 : ZMod 8) + 1) (5 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `7`, pre-tabulated. -/
def XLa3_1_5_7 : List (List (List ℤ)) :=
  [[[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]]]

/-- Left route at the `a`-slot generator `7`, pre-tabulated. -/
def YLa3_1_5_7 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca3_1_5_7 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_5_7 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_5_7 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_5_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_5_7 : ∀ I J g, Xa3_1_5_7 I J g = Xca3_1_5_7 I J g := by
  decide +kernel

theorem hYtaba3_1_5_7 : ∀ I J g, Ya3_1_5_7 I J g = Yca3_1_5_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `7`** (Koszul sign `-1`). -/
theorem hinta3_1_5_7 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_5
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_5 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xa3_1_5_7 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 hfuseZ_3_6 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xca3_1_5_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_5_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Ya3_1_5_7 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_3_1 hfuseZ_4_5 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Yca3_1_5_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_5_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 3 1 5).1 (realGauge.gaugeSizeL 3 1 5).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_5_7 TL3_1_5 YLa3_1_5_7 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb3_1_5_0 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_3_6 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 5) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb3_1_5_0 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((3 : ZMod 8) + 1) (5 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb3_1_5_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb3_1_5_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcb3_1_5_0 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb3_1_5_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_1_5_0 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb3_1_5_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_1_5_0 : ∀ I J g, Xb3_1_5_0 I J g = Xcb3_1_5_0 I J g := by
  decide +kernel

theorem hYtabb3_1_5_0 : ∀ I J g, Yb3_1_5_0 I J g = Ycb3_1_5_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb3_1_5_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T3_1_5
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_5 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xb3_1_5_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 hfuseZ_1_5 hfuseZ_3_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xcb3_1_5_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_1_5_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Yb3_1_5_0 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_3_1 hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Ycb3_1_5_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_1_5_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 3 1 5).1 (realGauge.gaugeSizeL 3 1 5).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb3_1_5_0 TL3_1_5 YLb3_1_5_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb3_1_5_1 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_3_6 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 5) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb3_1_5_1 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((3 : ZMod 8) + 1) (5 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb3_1_5_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb3_1_5_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb3_1_5_1 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb3_1_5_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_1_5_1 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb3_1_5_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_1_5_1 : ∀ I J g, Xb3_1_5_1 I J g = Xcb3_1_5_1 I J g := by
  decide +kernel

theorem hYtabb3_1_5_1 : ∀ I J g, Yb3_1_5_1 I J g = Ycb3_1_5_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintb3_1_5_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T3_1_5
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_5 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xb3_1_5_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 hfuseZ_1_5 hfuseZ_3_6 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xcb3_1_5_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_1_5_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Yb3_1_5_1 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_3_1 hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Ycb3_1_5_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_1_5_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 3 1 5).1 (realGauge.gaugeSizeL 3 1 5).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb3_1_5_1 TL3_1_5 YLb3_1_5_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc3_1_5_0 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_3_6 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 5) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc3_1_5_0 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) = (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow ((3 : ZMod 8) + 1) (5 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc3_1_5_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc3_1_5_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcc3_1_5_0 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc3_1_5_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_1_5_0 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc3_1_5_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_1_5_0 : ∀ I J g, Xc3_1_5_0 I J g = Xcc3_1_5_0 I J g := by
  decide +kernel

theorem hYtabc3_1_5_0 : ∀ I J g, Yc3_1_5_0 I J g = Ycc3_1_5_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc3_1_5_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T3_1_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_5 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xc3_1_5_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 hfuseZ_1_5 hfuseZ_3_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xcc3_1_5_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_1_5_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Yc3_1_5_0 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Ycc3_1_5_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_1_5_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 3 1 5).1 (realGauge.gaugeSizeL 3 1 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_1_5_0 TL3_1_5 YLc3_1_5_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc3_1_5_1 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_3_6 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 5) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc3_1_5_1 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) = (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow ((3 : ZMod 8) + 1) (5 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc3_1_5_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc3_1_5_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]]]

noncomputable def Xcc3_1_5_1 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc3_1_5_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_1_5_1 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc3_1_5_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_1_5_1 : ∀ I J g, Xc3_1_5_1 I J g = Xcc3_1_5_1 I J g := by
  decide +kernel

theorem hYtabc3_1_5_1 : ∀ I J g, Yc3_1_5_1 I J g = Ycc3_1_5_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintc3_1_5_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T3_1_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_5 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xc3_1_5_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 hfuseZ_1_5 hfuseZ_3_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xcc3_1_5_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_1_5_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Yc3_1_5_1 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Ycc3_1_5_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_1_5_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 3 1 5).1 (realGauge.gaugeSizeL 3 1 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_1_5_1 TL3_1_5 YLc3_1_5_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc3_1_5_2 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_3_6 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 5) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc3_1_5_2 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) = (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow ((3 : ZMod 8) + 1) (5 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc3_1_5_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc3_1_5_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc3_1_5_2 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc3_1_5_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_1_5_2 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc3_1_5_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_1_5_2 : ∀ I J g, Xc3_1_5_2 I J g = Xcc3_1_5_2 I J g := by
  decide +kernel

theorem hYtabc3_1_5_2 : ∀ I J g, Yc3_1_5_2 I J g = Ycc3_1_5_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintc3_1_5_2 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T3_1_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_5 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xc3_1_5_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 hfuseZ_1_5 hfuseZ_3_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xcc3_1_5_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_1_5_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Yc3_1_5_2 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Ycc3_1_5_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_1_5_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 3 1 5).1 (realGauge.gaugeSizeL 3 1 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_1_5_2 TL3_1_5 YLc3_1_5_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc3_1_5_3 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_3_6 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 5) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc3_1_5_3 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) = (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow ((3 : ZMod 8) + 1) (5 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc3_1_5_3 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc3_1_5_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc3_1_5_3 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc3_1_5_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_1_5_3 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc3_1_5_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_1_5_3 : ∀ I J g, Xc3_1_5_3 I J g = Xcc3_1_5_3 I J g := by
  decide +kernel

theorem hYtabc3_1_5_3 : ∀ I J g, Yc3_1_5_3 I J g = Ycc3_1_5_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc3_1_5_3 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T3_1_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_5 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xc3_1_5_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 hfuseZ_1_5 hfuseZ_3_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xcc3_1_5_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_1_5_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Yc3_1_5_3 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Ycc3_1_5_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_1_5_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 3 1 5).1 (realGauge.gaugeSizeL 3 1 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_1_5_3 TL3_1_5 YLc3_1_5_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Xc3_1_5_4 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_3_6 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 5) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Yc3_1_5_4 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) = (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow ((3 : ZMod 8) + 1) (5 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `4`, pre-tabulated. -/
def XLc3_1_5_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `4`, pre-tabulated. -/
def YLc3_1_5_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc3_1_5_4 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc3_1_5_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_1_5_4 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc3_1_5_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_1_5_4 : ∀ I J g, Xc3_1_5_4 I J g = Xcc3_1_5_4 I J g := by
  decide +kernel

theorem hYtabc3_1_5_4 : ∀ I J g, Yc3_1_5_4 I J g = Ycc3_1_5_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `4`** (Koszul sign `-1`). -/
theorem hintc3_1_5_4 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T3_1_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_5 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xc3_1_5_4 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 hfuseZ_1_5 hfuseZ_3_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xcc3_1_5_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_1_5_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Yc3_1_5_4 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Ycc3_1_5_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_1_5_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 3 1 5).1 (realGauge.gaugeSizeL 3 1 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_1_5_4 TL3_1_5 YLc3_1_5_4 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Xc3_1_5_5 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_3_6 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 5) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Yc3_1_5_5 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) = (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow ((3 : ZMod 8) + 1) (5 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `5`, pre-tabulated. -/
def XLc3_1_5_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `5`, pre-tabulated. -/
def YLc3_1_5_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc3_1_5_5 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc3_1_5_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_1_5_5 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc3_1_5_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_1_5_5 : ∀ I J g, Xc3_1_5_5 I J g = Xcc3_1_5_5 I J g := by
  decide +kernel

theorem hYtabc3_1_5_5 : ∀ I J g, Yc3_1_5_5 I J g = Ycc3_1_5_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintc3_1_5_5 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T3_1_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_5 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xc3_1_5_5 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 hfuseZ_1_5 hfuseZ_3_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xcc3_1_5_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_1_5_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Yc3_1_5_5 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Ycc3_1_5_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_1_5_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 3 1 5).1 (realGauge.gaugeSizeL 3 1 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_1_5_5 TL3_1_5 YLc3_1_5_5 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Xc3_1_5_6 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_3_6 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 5) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Yc3_1_5_6 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) = (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow ((3 : ZMod 8) + 1) (5 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `6`, pre-tabulated. -/
def XLc3_1_5_6 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `6`, pre-tabulated. -/
def YLc3_1_5_6 : List (List (List ℤ)) :=
  [[[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]]]

noncomputable def Xcc3_1_5_6 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc3_1_5_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_1_5_6 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc3_1_5_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_1_5_6 : ∀ I J g, Xc3_1_5_6 I J g = Xcc3_1_5_6 I J g := by
  decide +kernel

theorem hYtabc3_1_5_6 : ∀ I J g, Yc3_1_5_6 I J g = Ycc3_1_5_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintc3_1_5_6 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T3_1_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_5 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xc3_1_5_6 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 hfuseZ_1_5 hfuseZ_3_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xcc3_1_5_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_1_5_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Yc3_1_5_6 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Ycc3_1_5_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_1_5_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 3 1 5).1 (realGauge.gaugeSizeL 3 1 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_1_5_6 TL3_1_5 YLc3_1_5_6 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Xc3_1_5_7 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_5 (fuseRow (1 : ZMod 8) (5 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ro (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) ee) (fuseCol (1 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_3_6 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 5) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 I) (ri (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Yc3_1_5_7 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) = (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (lo (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow ((3 : ZMod 8) + 1) (5 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `7`, pre-tabulated. -/
def XLc3_1_5_7 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `7`, pre-tabulated. -/
def YLc3_1_5_7 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]]]

noncomputable def Xcc3_1_5_7 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc3_1_5_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_1_5_7 : (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc3_1_5_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_1_5_7 : ∀ I J g, Xc3_1_5_7 I J g = Xcc3_1_5_7 I J g := by
  decide +kernel

theorem hYtabc3_1_5_7 : ∀ I J g, Yc3_1_5_7 I J g = Ycc3_1_5_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `7`** (Koszul sign `-1`). -/
theorem hintc3_1_5_7 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T3_1_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_5 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xc3_1_5_7 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 hfuseZ_1_5 hfuseZ_3_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Xcc3_1_5_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_1_5_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Yc3_1_5_7 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 5)) Ycc3_1_5_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 5).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 5).2)) (realRepBasis ((3 : ZMod 8) + 1 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_1_5_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 5) (realGauge.gaugeSizeL 3 1 5).1 (realGauge.gaugeSizeL 3 1 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_1_5_7 TL3_1_5 YLc3_1_5_7 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint3_1_5 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T3_1_5
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T3_1_5 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hinta3_1_5_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hinta3_1_5_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hinta3_1_5_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hinta3_1_5_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hinta3_1_5_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hinta3_1_5_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hinta3_1_5_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hinta3_1_5_7

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint3_1_5 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T3_1_5
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T3_1_5 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hintb3_1_5_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hintb3_1_5_1

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint3_1_5 (i : Fin (realRepDim (5 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) i)) * T3_1_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T3_1_5 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h0]; exact hintc3_1_5_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h1]; exact hintc3_1_5_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h2]; exact hintc3_1_5_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h3]; exact hintc3_1_5_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h4]; exact hintc3_1_5_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h5]; exact hintc3_1_5_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h6]; exact hintc3_1_5_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h7]; exact hintc3_1_5_7

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT3_1_5_mem_gInterSpace :
    gtOfT ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 T3_1_5 ∈ gInterSpace ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 hT3_1_5 hAint3_1_5 hBint3_1_5 hCint3_1_5

theorem gtOfT3_1_5_ne_zero : gtOfT ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 T3_1_5 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) hsz3_1_5 T3_1_5_ne_zero

theorem gInterSpace3_1_5_ne_bot : gInterSpace ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT3_1_5_mem_gInterSpace, gtOfT3_1_5_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_3_1_5 : gParity ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (5 : ZMod 8) gInterSpace3_1_5_ne_bot).symm

end Triple_3_1_5

/-! ### The triple `(3,1,6)`

`gaugeSizeL = gaugeSizeR = (2,2)`, `dim D_2 = 4`, certgen parity `1`; the transported connector literal. -/
section Triple_3_1_6
open Module
theorem hsz3_1_6 : realGauge.gaugeSizeR 3 1 6 = realGauge.gaugeSizeL 3 1 6 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`4 x 4 x 4`). -/
def TL3_1_6 : List (List (List ℤ)) :=
  [[[0, -1, -1, 0], [0, 1, -1, 0], [-1, 0, 0, -1], [1, 0, 0, -1]],
   [[0, -1, 1, 0], [0, 1, 1, 0], [-1, 0, 0, 1], [1, 0, 0, 1]],
   [[1, 0, 0, -1], [1, 0, 0, 1], [0, 1, -1, 0], [0, 1, 1, 0]],
   [[1, 0, 0, 1], [1, 0, 0, -1], [0, 1, 1, 0], [0, 1, -1, 0]]]

/-- The same literal read at the composite frame `Fin 2 ⊕ Fin 2`. -/
noncomputable def Tc3_1_6 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet TL3_1_6 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_2`. -/
noncomputable def T3_1_6 : ((realGauge.D ((3 : ZMod 8) + 1 + 6)).matrixSuper
    (realGauge.gaugeSizeL 3 1 6).1 (realGauge.gaugeSizeL 3 1 6).2).carrier :=
  matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Tc3_1_6

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT3_1_6 : T3_1_6 ∈ ((realGauge.D ((3 : ZMod 8) + 1 + 6)).matrixSuper
    (realGauge.gaugeSizeL 3 1 6).1 (realGauge.gaugeSizeL 3 1 6).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((3 : ZMod 8) + 1 + 6) Tc3_1_6 1 (by decide)

theorem T3_1_6_ne_zero : T3_1_6 ≠ 0 :=
  matOfCoeff_ne_zero ((3 : ZMod 8) + 1 + 6) Tc3_1_6 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨1, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa3_1_6_0 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (6 : ZMod 8)).1 (realSize (1 : ZMod 8) (6 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I)
          * realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_7 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 6) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya3_1_6_0 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_6 (fuseRow ((3 : ZMod 8) + 1) (6 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa3_1_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa3_1_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xca3_1_6_0 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_6_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_6_0 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_6_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_6_0 : ∀ I J g, Xa3_1_6_0 I J g = Xca3_1_6_0 I J g := by
  decide +kernel

theorem hYtaba3_1_6_0 : ∀ I J g, Ya3_1_6_0 I J g = Yca3_1_6_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta3_1_6_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xa3_1_6_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 hfuseZ_3_7 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xca3_1_6_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_6_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Ya3_1_6_0 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hfuseZ_3_1 hfuseZ_4_6 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Yca3_1_6_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_6_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 6) (realGauge.gaugeSizeL 3 1 6).1 (realGauge.gaugeSizeL 3 1 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_6_0 TL3_1_6 YLa3_1_6_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa3_1_6_1 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (6 : ZMod 8)).1 (realSize (1 : ZMod 8) (6 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I)
          * realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_7 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 6) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 6) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya3_1_6_1 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_6 (fuseRow ((3 : ZMod 8) + 1) (6 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa3_1_6_1 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa3_1_6_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca3_1_6_1 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_6_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_6_1 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_6_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_6_1 : ∀ I J g, Xa3_1_6_1 I J g = Xca3_1_6_1 I J g := by
  decide +kernel

theorem hYtaba3_1_6_1 : ∀ I J g, Ya3_1_6_1 I J g = Yca3_1_6_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `-1`). -/
theorem hinta3_1_6_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xa3_1_6_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 hfuseZ_3_7 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xca3_1_6_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_6_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Ya3_1_6_1 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hfuseZ_3_1 hfuseZ_4_6 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Yca3_1_6_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_6_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 6) (realGauge.gaugeSizeL 3 1 6).1 (realGauge.gaugeSizeL 3 1 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_6_1 TL3_1_6 YLa3_1_6_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa3_1_6_2 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (6 : ZMod 8)).1 (realSize (1 : ZMod 8) (6 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I)
          * realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_7 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 6) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 6) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya3_1_6_2 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_6 (fuseRow ((3 : ZMod 8) + 1) (6 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa3_1_6_2 : List (List (List ℤ)) :=
  [[[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa3_1_6_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca3_1_6_2 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_6_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_6_2 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_6_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_6_2 : ∀ I J g, Xa3_1_6_2 I J g = Xca3_1_6_2 I J g := by
  decide +kernel

theorem hYtaba3_1_6_2 : ∀ I J g, Ya3_1_6_2 I J g = Yca3_1_6_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `-1`). -/
theorem hinta3_1_6_2 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xa3_1_6_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 hfuseZ_3_7 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xca3_1_6_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_6_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Ya3_1_6_2 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hfuseZ_3_1 hfuseZ_4_6 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Yca3_1_6_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_6_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 6) (realGauge.gaugeSizeL 3 1 6).1 (realGauge.gaugeSizeL 3 1 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_6_2 TL3_1_6 YLa3_1_6_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa3_1_6_3 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (6 : ZMod 8)).1 (realSize (1 : ZMod 8) (6 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I)
          * realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_7 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 6) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 6) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya3_1_6_3 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_6 (fuseRow ((3 : ZMod 8) + 1) (6 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa3_1_6_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa3_1_6_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca3_1_6_3 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_6_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_6_3 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_6_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_6_3 : ∀ I J g, Xa3_1_6_3 I J g = Xca3_1_6_3 I J g := by
  decide +kernel

theorem hYtaba3_1_6_3 : ∀ I J g, Ya3_1_6_3 I J g = Yca3_1_6_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta3_1_6_3 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xa3_1_6_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 hfuseZ_3_7 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xca3_1_6_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_6_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Ya3_1_6_3 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hfuseZ_3_1 hfuseZ_4_6 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Yca3_1_6_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_6_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 6) (realGauge.gaugeSizeL 3 1 6).1 (realGauge.gaugeSizeL 3 1 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_6_3 TL3_1_6 YLa3_1_6_3 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Xa3_1_6_4 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (6 : ZMod 8)).1 (realSize (1 : ZMod 8) (6 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I)
          * realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_7 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 6) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 6) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Ya3_1_6_4 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_6 (fuseRow ((3 : ZMod 8) + 1) (6 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `4`, pre-tabulated. -/
def XLa3_1_6_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `4`, pre-tabulated. -/
def YLa3_1_6_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca3_1_6_4 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_6_4 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_6_4 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_6_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_6_4 : ∀ I J g, Xa3_1_6_4 I J g = Xca3_1_6_4 I J g := by
  decide +kernel

theorem hYtaba3_1_6_4 : ∀ I J g, Ya3_1_6_4 I J g = Yca3_1_6_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `4`** (Koszul sign `-1`). -/
theorem hinta3_1_6_4 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xa3_1_6_4 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 hfuseZ_3_7 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xca3_1_6_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_6_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Ya3_1_6_4 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hfuseZ_3_1 hfuseZ_4_6 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Yca3_1_6_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_6_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 6) (realGauge.gaugeSizeL 3 1 6).1 (realGauge.gaugeSizeL 3 1 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_6_4 TL3_1_6 YLa3_1_6_4 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Xa3_1_6_5 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (6 : ZMod 8)).1 (realSize (1 : ZMod 8) (6 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I)
          * realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_7 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 6) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 6) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Ya3_1_6_5 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_6 (fuseRow ((3 : ZMod 8) + 1) (6 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `5`, pre-tabulated. -/
def XLa3_1_6_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `5`, pre-tabulated. -/
def YLa3_1_6_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca3_1_6_5 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_6_5 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_6_5 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_6_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_6_5 : ∀ I J g, Xa3_1_6_5 I J g = Xca3_1_6_5 I J g := by
  decide +kernel

theorem hYtaba3_1_6_5 : ∀ I J g, Ya3_1_6_5 I J g = Yca3_1_6_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `5`** (Koszul sign `+1`). -/
theorem hinta3_1_6_5 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xa3_1_6_5 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 hfuseZ_3_7 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xca3_1_6_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_6_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Ya3_1_6_5 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hfuseZ_3_1 hfuseZ_4_6 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Yca3_1_6_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_6_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 6) (realGauge.gaugeSizeL 3 1 6).1 (realGauge.gaugeSizeL 3 1 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_6_5 TL3_1_6 YLa3_1_6_5 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Xa3_1_6_6 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (6 : ZMod 8)).1 (realSize (1 : ZMod 8) (6 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I)
          * realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_7 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 6) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 6) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Ya3_1_6_6 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_6 (fuseRow ((3 : ZMod 8) + 1) (6 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `6`, pre-tabulated. -/
def XLa3_1_6_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `6`, pre-tabulated. -/
def YLa3_1_6_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1]]]

noncomputable def Xca3_1_6_6 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_6_6 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_6_6 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_6_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_6_6 : ∀ I J g, Xa3_1_6_6 I J g = Xca3_1_6_6 I J g := by
  decide +kernel

theorem hYtaba3_1_6_6 : ∀ I J g, Ya3_1_6_6 I J g = Yca3_1_6_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `6`** (Koszul sign `+1`). -/
theorem hinta3_1_6_6 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xa3_1_6_6 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 hfuseZ_3_7 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xca3_1_6_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_6_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Ya3_1_6_6 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hfuseZ_3_1 hfuseZ_4_6 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Yca3_1_6_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_6_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 6) (realGauge.gaugeSizeL 3 1 6).1 (realGauge.gaugeSizeL 3 1 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_6_6 TL3_1_6 YLa3_1_6_6 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Xa3_1_6_7 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (6 : ZMod 8)).1 (realSize (1 : ZMod 8) (6 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I)
          * realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_7 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 6) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 6) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Ya3_1_6_7 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_6 (fuseRow ((3 : ZMod 8) + 1) (6 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `7`, pre-tabulated. -/
def XLa3_1_6_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `7`, pre-tabulated. -/
def YLa3_1_6_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]]]

noncomputable def Xca3_1_6_7 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_6_7 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_6_7 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_6_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_6_7 : ∀ I J g, Xa3_1_6_7 I J g = Xca3_1_6_7 I J g := by
  decide +kernel

theorem hYtaba3_1_6_7 : ∀ I J g, Ya3_1_6_7 I J g = Yca3_1_6_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `7`** (Koszul sign `-1`). -/
theorem hinta3_1_6_7 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xa3_1_6_7 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 hfuseZ_3_7 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xca3_1_6_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_6_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Ya3_1_6_7 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hfuseZ_3_1 hfuseZ_4_6 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Yca3_1_6_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_6_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 6) (realGauge.gaugeSizeL 3 1 6).1 (realGauge.gaugeSizeL 3 1 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_1_6_7 TL3_1_6 YLa3_1_6_7 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb3_1_6_0 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_6 (fuseRow (1 : ZMod 8) (6 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) ee) (fuseCol (1 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_3_7 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 6) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb3_1_6_0 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_6 (fuseRow ((3 : ZMod 8) + 1) (6 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb3_1_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb3_1_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcb3_1_6_0 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb3_1_6_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_1_6_0 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb3_1_6_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_1_6_0 : ∀ I J g, Xb3_1_6_0 I J g = Xcb3_1_6_0 I J g := by
  decide +kernel

theorem hYtabb3_1_6_0 : ∀ I J g, Yb3_1_6_0 I J g = Ycb3_1_6_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb3_1_6_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T3_1_6
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xb3_1_6_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 hfuseZ_1_6 hfuseZ_3_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xcb3_1_6_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_1_6_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Yb3_1_6_0 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hfuseZ_3_1 hfuseZ_4_6 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Ycb3_1_6_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_1_6_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 6) (realGauge.gaugeSizeL 3 1 6).1 (realGauge.gaugeSizeL 3 1 6).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb3_1_6_0 TL3_1_6 YLb3_1_6_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb3_1_6_1 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_6 (fuseRow (1 : ZMod 8) (6 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) ee) (fuseCol (1 : ZMod 8) (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_3_7 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 6) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb3_1_6_1 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_6 (fuseRow ((3 : ZMod 8) + 1) (6 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb3_1_6_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb3_1_6_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]]]

noncomputable def Xcb3_1_6_1 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb3_1_6_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_1_6_1 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb3_1_6_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_1_6_1 : ∀ I J g, Xb3_1_6_1 I J g = Xcb3_1_6_1 I J g := by
  decide +kernel

theorem hYtabb3_1_6_1 : ∀ I J g, Yb3_1_6_1 I J g = Ycb3_1_6_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintb3_1_6_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T3_1_6
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xb3_1_6_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 hfuseZ_1_6 hfuseZ_3_7 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xcb3_1_6_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_1_6_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Yb3_1_6_1 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hfuseZ_3_1 hfuseZ_4_6 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Ycb3_1_6_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_1_6_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 6) (realGauge.gaugeSizeL 3 1 6).1 (realGauge.gaugeSizeL 3 1 6).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb3_1_6_1 TL3_1_6 YLb3_1_6_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc3_1_6_0 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_6 (fuseRow (1 : ZMod 8) (6 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) ee) (fuseCol (1 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_3_7 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 6) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc3_1_6_0 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) = (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_6 (fuseRow ((3 : ZMod 8) + 1) (6 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc3_1_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc3_1_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcc3_1_6_0 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc3_1_6_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_1_6_0 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc3_1_6_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_1_6_0 : ∀ I J g, Xc3_1_6_0 I J g = Xcc3_1_6_0 I J g := by
  decide +kernel

theorem hYtabc3_1_6_0 : ∀ I J g, Yc3_1_6_0 I J g = Ycc3_1_6_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc3_1_6_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T3_1_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xc3_1_6_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 hfuseZ_1_6 hfuseZ_3_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xcc3_1_6_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_1_6_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Yc3_1_6_0 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hfuseZ_4_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Ycc3_1_6_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_1_6_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 6) (realGauge.gaugeSizeL 3 1 6).1 (realGauge.gaugeSizeL 3 1 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_1_6_0 TL3_1_6 YLc3_1_6_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc3_1_6_1 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_6 (fuseRow (1 : ZMod 8) (6 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) ee) (fuseCol (1 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_3_7 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 6) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc3_1_6_1 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) = (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_6 (fuseRow ((3 : ZMod 8) + 1) (6 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc3_1_6_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc3_1_6_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc3_1_6_1 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc3_1_6_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_1_6_1 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc3_1_6_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_1_6_1 : ∀ I J g, Xc3_1_6_1 I J g = Xcc3_1_6_1 I J g := by
  decide +kernel

theorem hYtabc3_1_6_1 : ∀ I J g, Yc3_1_6_1 I J g = Ycc3_1_6_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintc3_1_6_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T3_1_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xc3_1_6_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 hfuseZ_1_6 hfuseZ_3_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xcc3_1_6_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_1_6_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Yc3_1_6_1 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hfuseZ_4_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Ycc3_1_6_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_1_6_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 6) (realGauge.gaugeSizeL 3 1 6).1 (realGauge.gaugeSizeL 3 1 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_1_6_1 TL3_1_6 YLc3_1_6_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc3_1_6_2 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_6 (fuseRow (1 : ZMod 8) (6 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) ee) (fuseCol (1 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_3_7 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 6) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc3_1_6_2 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) = (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_6 (fuseRow ((3 : ZMod 8) + 1) (6 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc3_1_6_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc3_1_6_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc3_1_6_2 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc3_1_6_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_1_6_2 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc3_1_6_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_1_6_2 : ∀ I J g, Xc3_1_6_2 I J g = Xcc3_1_6_2 I J g := by
  decide +kernel

theorem hYtabc3_1_6_2 : ∀ I J g, Yc3_1_6_2 I J g = Ycc3_1_6_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintc3_1_6_2 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T3_1_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xc3_1_6_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 hfuseZ_1_6 hfuseZ_3_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xcc3_1_6_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_1_6_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Yc3_1_6_2 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hfuseZ_4_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Ycc3_1_6_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_1_6_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 6) (realGauge.gaugeSizeL 3 1 6).1 (realGauge.gaugeSizeL 3 1 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_1_6_2 TL3_1_6 YLc3_1_6_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc3_1_6_3 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_6 (fuseRow (1 : ZMod 8) (6 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) (ro (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) ee) (fuseCol (1 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_3_7 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 6) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 I) (ri (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc3_1_6_3 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) = (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (lo (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_6 (fuseRow ((3 : ZMod 8) + 1) (6 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc3_1_6_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc3_1_6_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]]]

noncomputable def Xcc3_1_6_3 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc3_1_6_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_1_6_3 : (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc3_1_6_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_1_6_3 : ∀ I J g, Xc3_1_6_3 I J g = Xcc3_1_6_3 I J g := by
  decide +kernel

theorem hYtabc3_1_6_3 : ∀ I J g, Yc3_1_6_3 I J g = Ycc3_1_6_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc3_1_6_3 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T3_1_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_1_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xc3_1_6_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 hfuseZ_1_6 hfuseZ_3_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Xcc3_1_6_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_1_6_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Yc3_1_6_3 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hfuseZ_4_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 6)) Ycc3_1_6_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 6).2)) (realRepBasis ((3 : ZMod 8) + 1 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_1_6_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 6) (realGauge.gaugeSizeL 3 1 6).1 (realGauge.gaugeSizeL 3 1 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_1_6_3 TL3_1_6 YLc3_1_6_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint3_1_6 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T3_1_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T3_1_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hinta3_1_6_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hinta3_1_6_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hinta3_1_6_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hinta3_1_6_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hinta3_1_6_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hinta3_1_6_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hinta3_1_6_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hinta3_1_6_7

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint3_1_6 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T3_1_6
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T3_1_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hintb3_1_6_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hintb3_1_6_1

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint3_1_6 (i : Fin (realRepDim (6 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) i)) * T3_1_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T3_1_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h0]; exact hintc3_1_6_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h1]; exact hintc3_1_6_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h2]; exact hintc3_1_6_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h3]; exact hintc3_1_6_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT3_1_6_mem_gInterSpace :
    gtOfT ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 T3_1_6 ∈ gInterSpace ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 hT3_1_6 hAint3_1_6 hBint3_1_6 hCint3_1_6

theorem gtOfT3_1_6_ne_zero : gtOfT ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 T3_1_6 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) hsz3_1_6 T3_1_6_ne_zero

theorem gInterSpace3_1_6_ne_bot : gInterSpace ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT3_1_6_mem_gInterSpace, gtOfT3_1_6_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_3_1_6 : gParity ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (6 : ZMod 8) gInterSpace3_1_6_ne_bot).symm

end Triple_3_1_6

/-! ### The triple `(3,1,7)`

`gaugeSizeL = gaugeSizeR = (1,1)`, `dim D_3 = 8`, certgen parity `0`; the transported connector literal. -/
section Triple_3_1_7
open Module
theorem hsz3_1_7 : realGauge.gaugeSizeR 3 1 7 = realGauge.gaugeSizeL 3 1 7 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`2 x 2 x 8`). -/
def TL3_1_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, -1, 0, 0, -1, 0], [0, 0, 1, 0, 0, 0, 0, 1]],
   [[0, 1, 0, 0, 1, 0, 0, 0], [-1, 0, 0, 0, 0, -1, 0, 0]]]

/-- The same literal read at the composite frame `Fin 1 ⊕ Fin 1`. -/
noncomputable def Tc3_1_7 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun r s g => coeffGet TL3_1_7 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_3`. -/
noncomputable def T3_1_7 : ((realGauge.D ((3 : ZMod 8) + 1 + 7)).matrixSuper
    (realGauge.gaugeSizeL 3 1 7).1 (realGauge.gaugeSizeL 3 1 7).2).carrier :=
  matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Tc3_1_7

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT3_1_7 : T3_1_7 ∈ ((realGauge.D ((3 : ZMod 8) + 1 + 7)).matrixSuper
    (realGauge.gaugeSizeL 3 1 7).1 (realGauge.gaugeSizeL 3 1 7).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((3 : ZMod 8) + 1 + 7) Tc3_1_7 0 (by decide)

theorem T3_1_7_ne_zero : T3_1_7 ≠ 0 :=
  matOfCoeff_ne_zero ((3 : ZMod 8) + 1 + 7) Tc3_1_7 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨3, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa3_1_7_0 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (7 : ZMod 8)).1 (realSize (1 : ZMod 8) (7 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I)
          * realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 7) (ri (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I) (ri (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya3_1_7_0 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow ((3 : ZMod 8) + 1) (7 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa3_1_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa3_1_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca3_1_7_0 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_7_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_7_0 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_7_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_7_0 : ∀ I J g, Xa3_1_7_0 I J g = Xca3_1_7_0 I J g := by
  decide +kernel

theorem hYtaba3_1_7_0 : ∀ I J g, Ya3_1_7_0 I J g = Yca3_1_7_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta3_1_7_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_1_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Xa3_1_7_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 hfuseZ_3_0 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Xca3_1_7_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2)) (realRepBasis ((3 : ZMod 8) + 1 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_7_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Ya3_1_7_0 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hfuseZ_3_1 hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Yca3_1_7_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2)) (realRepBasis ((3 : ZMod 8) + 1 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_7_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 7) (realGauge.gaugeSizeL 3 1 7).1 (realGauge.gaugeSizeL 3 1 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_1_7_0 TL3_1_7 YLa3_1_7_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa3_1_7_1 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (7 : ZMod 8)).1 (realSize (1 : ZMod 8) (7 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I)
          * realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 7) (ri (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I) (ri (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 7) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya3_1_7_1 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow ((3 : ZMod 8) + 1) (7 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa3_1_7_1 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa3_1_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0]],
   [[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca3_1_7_1 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_7_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_7_1 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_7_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_7_1 : ∀ I J g, Xa3_1_7_1 I J g = Xca3_1_7_1 I J g := by
  decide +kernel

theorem hYtaba3_1_7_1 : ∀ I J g, Ya3_1_7_1 I J g = Yca3_1_7_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta3_1_7_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_1_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Xa3_1_7_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 hfuseZ_3_0 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Xca3_1_7_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2)) (realRepBasis ((3 : ZMod 8) + 1 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_7_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Ya3_1_7_1 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hfuseZ_3_1 hfuseZ_4_7 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Yca3_1_7_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2)) (realRepBasis ((3 : ZMod 8) + 1 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_7_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 7) (realGauge.gaugeSizeL 3 1 7).1 (realGauge.gaugeSizeL 3 1 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_1_7_1 TL3_1_7 YLa3_1_7_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa3_1_7_2 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (7 : ZMod 8)).1 (realSize (1 : ZMod 8) (7 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I)
          * realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 7) (ri (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I) (ri (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 7) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya3_1_7_2 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow ((3 : ZMod 8) + 1) (7 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa3_1_7_2 : List (List (List ℤ)) :=
  [[[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa3_1_7_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0]],
   [[0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca3_1_7_2 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_7_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_7_2 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_7_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_7_2 : ∀ I J g, Xa3_1_7_2 I J g = Xca3_1_7_2 I J g := by
  decide +kernel

theorem hYtaba3_1_7_2 : ∀ I J g, Ya3_1_7_2 I J g = Yca3_1_7_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta3_1_7_2 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_1_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Xa3_1_7_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 hfuseZ_3_0 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Xca3_1_7_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2)) (realRepBasis ((3 : ZMod 8) + 1 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_7_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Ya3_1_7_2 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hfuseZ_3_1 hfuseZ_4_7 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Yca3_1_7_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2)) (realRepBasis ((3 : ZMod 8) + 1 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_7_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 7) (realGauge.gaugeSizeL 3 1 7).1 (realGauge.gaugeSizeL 3 1 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_1_7_2 TL3_1_7 YLa3_1_7_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa3_1_7_3 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (7 : ZMod 8)).1 (realSize (1 : ZMod 8) (7 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I)
          * realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 7) (ri (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I) (ri (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 7) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya3_1_7_3 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow ((3 : ZMod 8) + 1) (7 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa3_1_7_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa3_1_7_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]]]

noncomputable def Xca3_1_7_3 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_7_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_7_3 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_7_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_7_3 : ∀ I J g, Xa3_1_7_3 I J g = Xca3_1_7_3 I J g := by
  decide +kernel

theorem hYtaba3_1_7_3 : ∀ I J g, Ya3_1_7_3 I J g = Yca3_1_7_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta3_1_7_3 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_1_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Xa3_1_7_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 hfuseZ_3_0 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Xca3_1_7_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2)) (realRepBasis ((3 : ZMod 8) + 1 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_7_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Ya3_1_7_3 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hfuseZ_3_1 hfuseZ_4_7 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Yca3_1_7_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2)) (realRepBasis ((3 : ZMod 8) + 1 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_7_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 7) (realGauge.gaugeSizeL 3 1 7).1 (realGauge.gaugeSizeL 3 1 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_1_7_3 TL3_1_7 YLa3_1_7_3 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Xa3_1_7_4 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (7 : ZMod 8)).1 (realSize (1 : ZMod 8) (7 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I)
          * realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 7) (ri (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I) (ri (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 7) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Ya3_1_7_4 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow ((3 : ZMod 8) + 1) (7 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `4`, pre-tabulated. -/
def XLa3_1_7_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `4`, pre-tabulated. -/
def YLa3_1_7_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca3_1_7_4 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_7_4 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_7_4 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_7_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_7_4 : ∀ I J g, Xa3_1_7_4 I J g = Xca3_1_7_4 I J g := by
  decide +kernel

theorem hYtaba3_1_7_4 : ∀ I J g, Ya3_1_7_4 I J g = Yca3_1_7_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `4`** (Koszul sign `+1`). -/
theorem hinta3_1_7_4 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_1_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Xa3_1_7_4 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 hfuseZ_3_0 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Xca3_1_7_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2)) (realRepBasis ((3 : ZMod 8) + 1 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_7_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Ya3_1_7_4 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hfuseZ_3_1 hfuseZ_4_7 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Yca3_1_7_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2)) (realRepBasis ((3 : ZMod 8) + 1 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_7_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 7) (realGauge.gaugeSizeL 3 1 7).1 (realGauge.gaugeSizeL 3 1 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_1_7_4 TL3_1_7 YLa3_1_7_4 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Xa3_1_7_5 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (7 : ZMod 8)).1 (realSize (1 : ZMod 8) (7 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I)
          * realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 7) (ri (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I) (ri (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 7) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Ya3_1_7_5 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow ((3 : ZMod 8) + 1) (7 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `5`, pre-tabulated. -/
def XLa3_1_7_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0]]]

/-- Left route at the `a`-slot generator `5`, pre-tabulated. -/
def YLa3_1_7_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0]]]

noncomputable def Xca3_1_7_5 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_7_5 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_7_5 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_7_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_7_5 : ∀ I J g, Xa3_1_7_5 I J g = Xca3_1_7_5 I J g := by
  decide +kernel

theorem hYtaba3_1_7_5 : ∀ I J g, Ya3_1_7_5 I J g = Yca3_1_7_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `5`** (Koszul sign `+1`). -/
theorem hinta3_1_7_5 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_1_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Xa3_1_7_5 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 hfuseZ_3_0 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Xca3_1_7_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2)) (realRepBasis ((3 : ZMod 8) + 1 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_7_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Ya3_1_7_5 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hfuseZ_3_1 hfuseZ_4_7 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Yca3_1_7_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2)) (realRepBasis ((3 : ZMod 8) + 1 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_7_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 7) (realGauge.gaugeSizeL 3 1 7).1 (realGauge.gaugeSizeL 3 1 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_1_7_5 TL3_1_7 YLa3_1_7_5 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Xa3_1_7_6 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (7 : ZMod 8)).1 (realSize (1 : ZMod 8) (7 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I)
          * realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 7) (ri (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I) (ri (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 7) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Ya3_1_7_6 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow ((3 : ZMod 8) + 1) (7 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `6`, pre-tabulated. -/
def XLa3_1_7_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]]]

/-- Left route at the `a`-slot generator `6`, pre-tabulated. -/
def YLa3_1_7_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0]]]

noncomputable def Xca3_1_7_6 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_7_6 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_7_6 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_7_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_7_6 : ∀ I J g, Xa3_1_7_6 I J g = Xca3_1_7_6 I J g := by
  decide +kernel

theorem hYtaba3_1_7_6 : ∀ I J g, Ya3_1_7_6 I J g = Yca3_1_7_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `6`** (Koszul sign `+1`). -/
theorem hinta3_1_7_6 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_1_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Xa3_1_7_6 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 hfuseZ_3_0 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Xca3_1_7_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2)) (realRepBasis ((3 : ZMod 8) + 1 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_7_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Ya3_1_7_6 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hfuseZ_3_1 hfuseZ_4_7 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Yca3_1_7_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2)) (realRepBasis ((3 : ZMod 8) + 1 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_7_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 7) (realGauge.gaugeSizeL 3 1 7).1 (realGauge.gaugeSizeL 3 1 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_1_7_6 TL3_1_7 YLa3_1_7_6 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Xa3_1_7_7 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I) = (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (7 : ZMod 8)).1 (realSize (1 : ZMod 8) (7 : ZMod 8)).2 (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I)
          * realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 7) (ri (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I) (ri (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 7) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Ya3_1_7_7 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow ((3 : ZMod 8) + 1) (7 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `7`, pre-tabulated. -/
def XLa3_1_7_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]]]

/-- Left route at the `a`-slot generator `7`, pre-tabulated. -/
def YLa3_1_7_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]],
   [[0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca3_1_7_7 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa3_1_7_7 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_1_7_7 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa3_1_7_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_1_7_7 : ∀ I J g, Xa3_1_7_7 I J g = Xca3_1_7_7 I J g := by
  decide +kernel

theorem hYtaba3_1_7_7 : ∀ I J g, Ya3_1_7_7 I J g = Yca3_1_7_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `7`** (Koszul sign `+1`). -/
theorem hinta3_1_7_7 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_1_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_1_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Xa3_1_7_7 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 hfuseZ_3_0 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Xca3_1_7_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2)) (realRepBasis ((3 : ZMod 8) + 1 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_1_7_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Ya3_1_7_7 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hfuseZ_3_1 hfuseZ_4_7 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Yca3_1_7_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2)) (realRepBasis ((3 : ZMod 8) + 1 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_1_7_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 7) (realGauge.gaugeSizeL 3 1 7).1 (realGauge.gaugeSizeL 3 1 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_1_7_7 TL3_1_7 YLa3_1_7_7 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb3_1_7_0 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_7 (fuseRow (1 : ZMod 8) (7 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I) (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 J) ee) (fuseCol (1 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 7) (ri (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I) (ri (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb3_1_7_0 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow ((3 : ZMod 8) + 1) (7 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb3_1_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb3_1_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb3_1_7_0 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb3_1_7_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_1_7_0 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb3_1_7_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_1_7_0 : ∀ I J g, Xb3_1_7_0 I J g = Xcb3_1_7_0 I J g := by
  decide +kernel

theorem hYtabb3_1_7_0 : ∀ I J g, Yb3_1_7_0 I J g = Ycb3_1_7_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb3_1_7_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T3_1_7
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_1_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Xb3_1_7_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 hfuseZ_1_7 hfuseZ_3_0 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Xcb3_1_7_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2)) (realRepBasis ((3 : ZMod 8) + 1 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_1_7_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Yb3_1_7_0 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hfuseZ_3_1 hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Ycb3_1_7_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2)) (realRepBasis ((3 : ZMod 8) + 1 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_1_7_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 7) (realGauge.gaugeSizeL 3 1 7).1 (realGauge.gaugeSizeL 3 1 7).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb3_1_7_0 TL3_1_7 YLb3_1_7_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb3_1_7_1 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_7 (fuseRow (1 : ZMod 8) (7 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I) (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 J) ee) (fuseCol (1 : ZMod 8) (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 7) (ri (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I) (ri (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb3_1_7_1 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_1 (fuseRow (3 : ZMod 8) (1 : ZMod 8) (lo (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) I) (lo (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow ((3 : ZMod 8) + 1) (7 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb3_1_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb3_1_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, -1, 0]],
   [[0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb3_1_7_1 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb3_1_7_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_1_7_1 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb3_1_7_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_1_7_1 : ∀ I J g, Xb3_1_7_1 I J g = Xcb3_1_7_1 I J g := by
  decide +kernel

theorem hYtabb3_1_7_1 : ∀ I J g, Yb3_1_7_1 I J g = Ycb3_1_7_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb3_1_7_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T3_1_7
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_1_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Xb3_1_7_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 hfuseZ_1_7 hfuseZ_3_0 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Xcb3_1_7_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2)) (realRepBasis ((3 : ZMod 8) + 1 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_1_7_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Yb3_1_7_1 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hfuseZ_3_1 hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Ycb3_1_7_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2)) (realRepBasis ((3 : ZMod 8) + 1 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_1_7_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 7) (realGauge.gaugeSizeL 3 1 7).1 (realGauge.gaugeSizeL 3 1 7).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb3_1_7_1 TL3_1_7 YLb3_1_7_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc3_1_7_0 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_7 (fuseRow (1 : ZMod 8) (7 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I) (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 J) ee) (fuseCol (1 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 7) (ri (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I) (ri (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc3_1_7_0 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) I) = (lo (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (lo (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) I)
          * realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_7 (fuseRow ((3 : ZMod 8) + 1) (7 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc3_1_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc3_1_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcc3_1_7_0 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun r s g => coeffGet XLc3_1_7_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_1_7_0 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun r s g => coeffGet YLc3_1_7_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_1_7_0 : ∀ I J g, Xc3_1_7_0 I J g = Xcc3_1_7_0 I J g := by
  decide +kernel

theorem hYtabc3_1_7_0 : ∀ I J g, Yc3_1_7_0 I J g = Ycc3_1_7_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc3_1_7_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T3_1_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_1_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Xc3_1_7_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 hfuseZ_1_7 hfuseZ_3_0 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Xcc3_1_7_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2)) (realRepBasis ((3 : ZMod 8) + 1 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_1_7_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Yc3_1_7_0 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Ycc3_1_7_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2)) (realRepBasis ((3 : ZMod 8) + 1 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_1_7_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 7) (realGauge.gaugeSizeL 3 1 7).1 (realGauge.gaugeSizeL 3 1 7).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc3_1_7_0 TL3_1_7 YLc3_1_7_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc3_1_7_1 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_7 (fuseRow (1 : ZMod 8) (7 : ZMod 8) (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I) (ro (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 J) ee) (fuseCol (1 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((1 : ZMod 8) + 7) (ri (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 I) (ri (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 J) g) (fuseCol (3 : ZMod 8) ((1 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc3_1_7_1 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) I) = (lo (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (1 : ZMod 8)).1 (realSize (3 : ZMod 8) (1 : ZMod 8)).2 (lo (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) I)
          * realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_7 (fuseRow ((3 : ZMod 8) + 1) (7 : ZMod 8) (li (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) I) (li (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 1) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc3_1_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc3_1_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]]]

noncomputable def Xcc3_1_7_1 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun r s g => coeffGet XLc3_1_7_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_1_7_1 : (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2) → Fin (realRepDim ((3 : ZMod 8) + 1 + 7).val) → ℤ :=
  fun r s g => coeffGet YLc3_1_7_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_1_7_1 : ∀ I J g, Xc3_1_7_1 I J g = Xcc3_1_7_1 I J g := by
  decide +kernel

theorem hYtabc3_1_7_1 : ∀ I J g, Yc3_1_7_1 I J g = Ycc3_1_7_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc3_1_7_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T3_1_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_1_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Xc3_1_7_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 hfuseZ_1_7 hfuseZ_3_0 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Xcc3_1_7_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2)) (realRepBasis ((3 : ZMod 8) + 1 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_1_7_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Yc3_1_7_1 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 1 + 7)) Ycc3_1_7_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 1 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 1 7).2)) (realRepBasis ((3 : ZMod 8) + 1 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_1_7_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 1 + 7) (realGauge.gaugeSizeL 3 1 7).1 (realGauge.gaugeSizeL 3 1 7).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc3_1_7_1 TL3_1_7 YLc3_1_7_1 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint3_1_7 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T3_1_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T3_1_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hinta3_1_7_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hinta3_1_7_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hinta3_1_7_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hinta3_1_7_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hinta3_1_7_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hinta3_1_7_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hinta3_1_7_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hinta3_1_7_7

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint3_1_7 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T3_1_7
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T3_1_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hintb3_1_7_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hintb3_1_7_1

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint3_1_7 (i : Fin (realRepDim (7 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) i)) * T3_1_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T3_1_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h0]; exact hintc3_1_7_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h1]; exact hintc3_1_7_1

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT3_1_7_mem_gInterSpace :
    gtOfT ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 T3_1_7 ∈ gInterSpace ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 hT3_1_7 hAint3_1_7 hBint3_1_7 hCint3_1_7

theorem gtOfT3_1_7_ne_zero : gtOfT ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 T3_1_7 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) hsz3_1_7 T3_1_7_ne_zero

theorem gInterSpace3_1_7_ne_bot : gInterSpace ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT3_1_7_mem_gInterSpace, gtOfT3_1_7_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_3_1_7 : gParity ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (3 : ZMod 8) (1 : ZMod 8) (7 : ZMod 8) gInterSpace3_1_7_ne_bot).symm

end Triple_3_1_7

/-! ### The triple `(3,2,0)`

`gaugeSizeL = gaugeSizeR = (1,1)`, `dim D_5 = 8`, certgen parity `0`; the unit-slot shortcut: the connector is the identity, so every certificate carries the sign `+1`. -/
section Triple_3_2_0
open Module
theorem hsz3_2_0 : realGauge.gaugeSizeR 3 2 0 = realGauge.gaugeSizeL 3 2 0 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`2 x 2 x 8`). -/
def TL3_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- The same literal read at the composite frame `Fin 1 ⊕ Fin 1`. -/
noncomputable def Tc3_2_0 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun r s g => coeffGet TL3_2_0 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_5`. -/
noncomputable def T3_2_0 : ((realGauge.D ((3 : ZMod 8) + 2 + 0)).matrixSuper
    (realGauge.gaugeSizeL 3 2 0).1 (realGauge.gaugeSizeL 3 2 0).2).carrier :=
  matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Tc3_2_0

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT3_2_0 : T3_2_0 ∈ ((realGauge.D ((3 : ZMod 8) + 2 + 0)).matrixSuper
    (realGauge.gaugeSizeL 3 2 0).1 (realGauge.gaugeSizeL 3 2 0).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((3 : ZMod 8) + 2 + 0) Tc3_2_0 0 (by decide)

theorem T3_2_0_ne_zero : T3_2_0 ≠ 0 :=
  matOfCoeff_ne_zero ((3 : ZMod 8) + 2 + 0) Tc3_2_0 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa3_2_0_0 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I) = (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (0 : ZMod 8)).1 (realSize (2 : ZMod 8) (0 : ZMod 8)).2 (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I)
          * realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 0) (ri (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I) (ri (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya3_2_0_0 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (lo (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) I) (lo (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_0 (fuseRow ((3 : ZMod 8) + 2) (0 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa3_2_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa3_2_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca3_2_0_0 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa3_2_0_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_2_0_0 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa3_2_0_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_2_0_0 : ∀ I J g, Xa3_2_0_0 I J g = Xca3_2_0_0 I J g := by
  decide +kernel

theorem hYtaba3_2_0_0 : ∀ I J g, Ya3_2_0_0 I J g = Yca3_2_0_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta3_2_0_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_2_0
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_2_0 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Xa3_2_0_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 hfuseZ_3_2 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Xca3_2_0_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2)) (realRepBasis ((3 : ZMod 8) + 2 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_2_0_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Ya3_2_0_0 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hfuseZ_3_2 hfuseZ_5_0 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Yca3_2_0_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2)) (realRepBasis ((3 : ZMod 8) + 2 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_2_0_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 0) (realGauge.gaugeSizeL 3 2 0).1 (realGauge.gaugeSizeL 3 2 0).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_2_0_0 TL3_2_0 YLa3_2_0_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa3_2_0_1 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I) = (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (0 : ZMod 8)).1 (realSize (2 : ZMod 8) (0 : ZMod 8)).2 (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I)
          * realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 0) (ri (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I) (ri (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 0) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya3_2_0_1 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (lo (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) I) (lo (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_0 (fuseRow ((3 : ZMod 8) + 2) (0 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa3_2_0_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0]],
   [[0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa3_2_0_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0]],
   [[0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca3_2_0_1 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa3_2_0_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_2_0_1 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa3_2_0_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_2_0_1 : ∀ I J g, Xa3_2_0_1 I J g = Xca3_2_0_1 I J g := by
  decide +kernel

theorem hYtaba3_2_0_1 : ∀ I J g, Ya3_2_0_1 I J g = Yca3_2_0_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta3_2_0_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_2_0
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_2_0 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Xa3_2_0_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 hfuseZ_3_2 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Xca3_2_0_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2)) (realRepBasis ((3 : ZMod 8) + 2 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_2_0_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Ya3_2_0_1 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hfuseZ_3_2 hfuseZ_5_0 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Yca3_2_0_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2)) (realRepBasis ((3 : ZMod 8) + 2 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_2_0_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 0) (realGauge.gaugeSizeL 3 2 0).1 (realGauge.gaugeSizeL 3 2 0).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_2_0_1 TL3_2_0 YLa3_2_0_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa3_2_0_2 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I) = (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (0 : ZMod 8)).1 (realSize (2 : ZMod 8) (0 : ZMod 8)).2 (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I)
          * realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 0) (ri (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I) (ri (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 0) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya3_2_0_2 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (lo (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) I) (lo (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_0 (fuseRow ((3 : ZMod 8) + 2) (0 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa3_2_0_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa3_2_0_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca3_2_0_2 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa3_2_0_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_2_0_2 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa3_2_0_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_2_0_2 : ∀ I J g, Xa3_2_0_2 I J g = Xca3_2_0_2 I J g := by
  decide +kernel

theorem hYtaba3_2_0_2 : ∀ I J g, Ya3_2_0_2 I J g = Yca3_2_0_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta3_2_0_2 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_2_0
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_2_0 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Xa3_2_0_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 hfuseZ_3_2 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Xca3_2_0_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2)) (realRepBasis ((3 : ZMod 8) + 2 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_2_0_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Ya3_2_0_2 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hfuseZ_3_2 hfuseZ_5_0 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Yca3_2_0_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2)) (realRepBasis ((3 : ZMod 8) + 2 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_2_0_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 0) (realGauge.gaugeSizeL 3 2 0).1 (realGauge.gaugeSizeL 3 2 0).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_2_0_2 TL3_2_0 YLa3_2_0_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa3_2_0_3 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I) = (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (0 : ZMod 8)).1 (realSize (2 : ZMod 8) (0 : ZMod 8)).2 (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I)
          * realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 0) (ri (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I) (ri (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 0) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya3_2_0_3 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (lo (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) I) (lo (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_0 (fuseRow ((3 : ZMod 8) + 2) (0 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa3_2_0_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa3_2_0_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0]]]

noncomputable def Xca3_2_0_3 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa3_2_0_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_2_0_3 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa3_2_0_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_2_0_3 : ∀ I J g, Xa3_2_0_3 I J g = Xca3_2_0_3 I J g := by
  decide +kernel

theorem hYtaba3_2_0_3 : ∀ I J g, Ya3_2_0_3 I J g = Yca3_2_0_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta3_2_0_3 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_2_0
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_2_0 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Xa3_2_0_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 hfuseZ_3_2 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Xca3_2_0_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2)) (realRepBasis ((3 : ZMod 8) + 2 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_2_0_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Ya3_2_0_3 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hfuseZ_3_2 hfuseZ_5_0 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Yca3_2_0_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2)) (realRepBasis ((3 : ZMod 8) + 2 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_2_0_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 0) (realGauge.gaugeSizeL 3 2 0).1 (realGauge.gaugeSizeL 3 2 0).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_2_0_3 TL3_2_0 YLa3_2_0_3 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Xa3_2_0_4 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I) = (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (0 : ZMod 8)).1 (realSize (2 : ZMod 8) (0 : ZMod 8)).2 (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I)
          * realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 0) (ri (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I) (ri (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 0) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Ya3_2_0_4 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (lo (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) I) (lo (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_0 (fuseRow ((3 : ZMod 8) + 2) (0 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `4`, pre-tabulated. -/
def XLa3_2_0_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]]]

/-- Left route at the `a`-slot generator `4`, pre-tabulated. -/
def YLa3_2_0_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]]]

noncomputable def Xca3_2_0_4 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa3_2_0_4 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_2_0_4 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa3_2_0_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_2_0_4 : ∀ I J g, Xa3_2_0_4 I J g = Xca3_2_0_4 I J g := by
  decide +kernel

theorem hYtaba3_2_0_4 : ∀ I J g, Ya3_2_0_4 I J g = Yca3_2_0_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `4`** (Koszul sign `+1`). -/
theorem hinta3_2_0_4 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_2_0
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_2_0 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Xa3_2_0_4 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 hfuseZ_3_2 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Xca3_2_0_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2)) (realRepBasis ((3 : ZMod 8) + 2 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_2_0_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Ya3_2_0_4 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hfuseZ_3_2 hfuseZ_5_0 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Yca3_2_0_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2)) (realRepBasis ((3 : ZMod 8) + 2 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_2_0_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 0) (realGauge.gaugeSizeL 3 2 0).1 (realGauge.gaugeSizeL 3 2 0).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_2_0_4 TL3_2_0 YLa3_2_0_4 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Xa3_2_0_5 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I) = (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (0 : ZMod 8)).1 (realSize (2 : ZMod 8) (0 : ZMod 8)).2 (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I)
          * realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 0) (ri (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I) (ri (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 0) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Ya3_2_0_5 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (lo (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) I) (lo (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_0 (fuseRow ((3 : ZMod 8) + 2) (0 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `5`, pre-tabulated. -/
def XLa3_2_0_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0]],
   [[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `5`, pre-tabulated. -/
def YLa3_2_0_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0]],
   [[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca3_2_0_5 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa3_2_0_5 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_2_0_5 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa3_2_0_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_2_0_5 : ∀ I J g, Xa3_2_0_5 I J g = Xca3_2_0_5 I J g := by
  decide +kernel

theorem hYtaba3_2_0_5 : ∀ I J g, Ya3_2_0_5 I J g = Yca3_2_0_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `5`** (Koszul sign `+1`). -/
theorem hinta3_2_0_5 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_2_0
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_2_0 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Xa3_2_0_5 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 hfuseZ_3_2 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Xca3_2_0_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2)) (realRepBasis ((3 : ZMod 8) + 2 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_2_0_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Ya3_2_0_5 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hfuseZ_3_2 hfuseZ_5_0 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Yca3_2_0_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2)) (realRepBasis ((3 : ZMod 8) + 2 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_2_0_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 0) (realGauge.gaugeSizeL 3 2 0).1 (realGauge.gaugeSizeL 3 2 0).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_2_0_5 TL3_2_0 YLa3_2_0_5 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Xa3_2_0_6 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I) = (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (0 : ZMod 8)).1 (realSize (2 : ZMod 8) (0 : ZMod 8)).2 (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I)
          * realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 0) (ri (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I) (ri (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 0) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Ya3_2_0_6 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (lo (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) I) (lo (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_0 (fuseRow ((3 : ZMod 8) + 2) (0 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `6`, pre-tabulated. -/
def XLa3_2_0_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]],
   [[0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `6`, pre-tabulated. -/
def YLa3_2_0_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]],
   [[0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca3_2_0_6 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa3_2_0_6 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_2_0_6 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa3_2_0_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_2_0_6 : ∀ I J g, Xa3_2_0_6 I J g = Xca3_2_0_6 I J g := by
  decide +kernel

theorem hYtaba3_2_0_6 : ∀ I J g, Ya3_2_0_6 I J g = Yca3_2_0_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `6`** (Koszul sign `+1`). -/
theorem hinta3_2_0_6 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_2_0
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_2_0 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Xa3_2_0_6 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 hfuseZ_3_2 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Xca3_2_0_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2)) (realRepBasis ((3 : ZMod 8) + 2 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_2_0_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Ya3_2_0_6 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hfuseZ_3_2 hfuseZ_5_0 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Yca3_2_0_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2)) (realRepBasis ((3 : ZMod 8) + 2 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_2_0_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 0) (realGauge.gaugeSizeL 3 2 0).1 (realGauge.gaugeSizeL 3 2 0).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_2_0_6 TL3_2_0 YLa3_2_0_6 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Xa3_2_0_7 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I) = (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (0 : ZMod 8)).1 (realSize (2 : ZMod 8) (0 : ZMod 8)).2 (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I)
          * realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 0) (ri (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I) (ri (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 0) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Ya3_2_0_7 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (lo (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) I) (lo (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_0 (fuseRow ((3 : ZMod 8) + 2) (0 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `7`, pre-tabulated. -/
def XLa3_2_0_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `7`, pre-tabulated. -/
def YLa3_2_0_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0]]]

noncomputable def Xca3_2_0_7 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa3_2_0_7 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_2_0_7 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa3_2_0_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_2_0_7 : ∀ I J g, Xa3_2_0_7 I J g = Xca3_2_0_7 I J g := by
  decide +kernel

theorem hYtaba3_2_0_7 : ∀ I J g, Ya3_2_0_7 I J g = Yca3_2_0_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `7`** (Koszul sign `+1`). -/
theorem hinta3_2_0_7 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_2_0
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_2_0 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Xa3_2_0_7 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 hfuseZ_3_2 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Xca3_2_0_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2)) (realRepBasis ((3 : ZMod 8) + 2 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_2_0_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Ya3_2_0_7 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hfuseZ_3_2 hfuseZ_5_0 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Yca3_2_0_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2)) (realRepBasis ((3 : ZMod 8) + 2 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_2_0_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 0) (realGauge.gaugeSizeL 3 2 0).1 (realGauge.gaugeSizeL 3 2 0).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_2_0_7 TL3_2_0 YLa3_2_0_7 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb3_2_0_0 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_0 (fuseRow (2 : ZMod 8) (0 : ZMod 8) (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I) (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 J) ee) (fuseCol (2 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 0) (ri (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I) (ri (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb3_2_0_0 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (lo (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) I) (lo (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_0 (fuseRow ((3 : ZMod 8) + 2) (0 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb3_2_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb3_2_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb3_2_0_0 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb3_2_0_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_2_0_0 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb3_2_0_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_2_0_0 : ∀ I J g, Xb3_2_0_0 I J g = Xcb3_2_0_0 I J g := by
  decide +kernel

theorem hYtabb3_2_0_0 : ∀ I J g, Yb3_2_0_0 I J g = Ycb3_2_0_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb3_2_0_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T3_2_0
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_2_0 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Xb3_2_0_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 hfuseZ_2_0 hfuseZ_3_2 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Xcb3_2_0_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2)) (realRepBasis ((3 : ZMod 8) + 2 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_2_0_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Yb3_2_0_0 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hfuseZ_3_2 hfuseZ_5_0 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Ycb3_2_0_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2)) (realRepBasis ((3 : ZMod 8) + 2 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_2_0_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 0) (realGauge.gaugeSizeL 3 2 0).1 (realGauge.gaugeSizeL 3 2 0).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb3_2_0_0 TL3_2_0 YLb3_2_0_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb3_2_0_1 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_0 (fuseRow (2 : ZMod 8) (0 : ZMod 8) (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I) (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 J) ee) (fuseCol (2 : ZMod 8) (0 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 0) (ri (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I) (ri (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb3_2_0_1 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (lo (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) I) (lo (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_0 (fuseRow ((3 : ZMod 8) + 2) (0 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb3_2_0_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, -1, 0]],
   [[0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb3_2_0_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, -1, 0]],
   [[0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb3_2_0_1 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb3_2_0_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_2_0_1 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb3_2_0_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_2_0_1 : ∀ I J g, Xb3_2_0_1 I J g = Xcb3_2_0_1 I J g := by
  decide +kernel

theorem hYtabb3_2_0_1 : ∀ I J g, Yb3_2_0_1 I J g = Ycb3_2_0_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb3_2_0_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T3_2_0
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_2_0 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Xb3_2_0_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 hfuseZ_2_0 hfuseZ_3_2 (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Xcb3_2_0_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2)) (realRepBasis ((3 : ZMod 8) + 2 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_2_0_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Yb3_2_0_1 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hfuseZ_3_2 hfuseZ_5_0 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Ycb3_2_0_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2)) (realRepBasis ((3 : ZMod 8) + 2 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_2_0_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 0) (realGauge.gaugeSizeL 3 2 0).1 (realGauge.gaugeSizeL 3 2 0).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb3_2_0_1 TL3_2_0 YLb3_2_0_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb3_2_0_2 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_0 (fuseRow (2 : ZMod 8) (0 : ZMod 8) (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I) (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 J) ee) (fuseCol (2 : ZMod 8) (0 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 0) (ri (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I) (ri (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb3_2_0_2 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (lo (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) I) (lo (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_0 (fuseRow ((3 : ZMod 8) + 2) (0 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb3_2_0_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0]],
   [[0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb3_2_0_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0]],
   [[0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb3_2_0_2 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb3_2_0_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_2_0_2 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb3_2_0_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_2_0_2 : ∀ I J g, Xb3_2_0_2 I J g = Xcb3_2_0_2 I J g := by
  decide +kernel

theorem hYtabb3_2_0_2 : ∀ I J g, Yb3_2_0_2 I J g = Ycb3_2_0_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb3_2_0_2 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T3_2_0
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_2_0 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Xb3_2_0_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 hfuseZ_2_0 hfuseZ_3_2 (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Xcb3_2_0_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2)) (realRepBasis ((3 : ZMod 8) + 2 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_2_0_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Yb3_2_0_2 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hfuseZ_3_2 hfuseZ_5_0 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Ycb3_2_0_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2)) (realRepBasis ((3 : ZMod 8) + 2 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_2_0_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 0) (realGauge.gaugeSizeL 3 2 0).1 (realGauge.gaugeSizeL 3 2 0).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb3_2_0_2 TL3_2_0 YLb3_2_0_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb3_2_0_3 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_0 (fuseRow (2 : ZMod 8) (0 : ZMod 8) (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I) (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 J) ee) (fuseCol (2 : ZMod 8) (0 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 0) (ri (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I) (ri (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb3_2_0_3 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (lo (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) I) (lo (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_0 (fuseRow ((3 : ZMod 8) + 2) (0 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb3_2_0_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb3_2_0_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]]]

noncomputable def Xcb3_2_0_3 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb3_2_0_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_2_0_3 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb3_2_0_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_2_0_3 : ∀ I J g, Xb3_2_0_3 I J g = Xcb3_2_0_3 I J g := by
  decide +kernel

theorem hYtabb3_2_0_3 : ∀ I J g, Yb3_2_0_3 I J g = Ycb3_2_0_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb3_2_0_3 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T3_2_0
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_2_0 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Xb3_2_0_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 hfuseZ_2_0 hfuseZ_3_2 (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Xcb3_2_0_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2)) (realRepBasis ((3 : ZMod 8) + 2 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_2_0_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Yb3_2_0_3 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hfuseZ_3_2 hfuseZ_5_0 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Ycb3_2_0_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2)) (realRepBasis ((3 : ZMod 8) + 2 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_2_0_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 0) (realGauge.gaugeSizeL 3 2 0).1 (realGauge.gaugeSizeL 3 2 0).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb3_2_0_3 TL3_2_0 YLb3_2_0_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc3_2_0_0 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_0 (fuseRow (2 : ZMod 8) (0 : ZMod 8) (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I) (ro (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 J) ee) (fuseCol (2 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 0) (ri (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 I) (ri (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc3_2_0_0 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) I) = (lo (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (2 : ZMod 8)).1 (realSize (3 : ZMod 8) (2 : ZMod 8)).2 (lo (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) I)
          * realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_0 (fuseRow ((3 : ZMod 8) + 2) (0 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc3_2_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc3_2_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcc3_2_0_0 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun r s g => coeffGet XLc3_2_0_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_2_0_0 : (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 0).val) → ℤ :=
  fun r s g => coeffGet YLc3_2_0_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_2_0_0 : ∀ I J g, Xc3_2_0_0 I J g = Xcc3_2_0_0 I J g := by
  decide +kernel

theorem hYtabc3_2_0_0 : ∀ I J g, Yc3_2_0_0 I J g = Ycc3_2_0_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc3_2_0_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))) * T3_2_0
      = ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_2_0 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Xc3_2_0_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 hfuseZ_2_0 hfuseZ_3_2 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Xcc3_2_0_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2)) (realRepBasis ((3 : ZMod 8) + 2 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_2_0_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Yc3_2_0_0 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hfuseZ_5_0 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 0)) Ycc3_2_0_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 0).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 0).2)) (realRepBasis ((3 : ZMod 8) + 2 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_2_0_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 0) (realGauge.gaugeSizeL 3 2 0).1 (realGauge.gaugeSizeL 3 2 0).2 ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc3_2_0_0 TL3_2_0 YLc3_2_0_0 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint3_2_0 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T3_2_0
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T3_2_0 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hinta3_2_0_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hinta3_2_0_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hinta3_2_0_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hinta3_2_0_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hinta3_2_0_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hinta3_2_0_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hinta3_2_0_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hinta3_2_0_7

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint3_2_0 (i : Fin (realRepDim (2 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) i)) * T3_2_0
      = ((sgn (realRepBasisParity (2 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T3_2_0 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h0]; exact hintb3_2_0_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h1]; exact hintb3_2_0_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h2]; exact hintb3_2_0_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h3]; exact hintb3_2_0_3

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint3_2_0 (i : Fin (realRepDim (0 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) i)) * T3_2_0
      = ((sgn (realRepBasisParity (0 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T3_2_0 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 1 := i.isLt
  have h0 : (i : ℕ) = 0 := by omega
  rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) from Fin.ext h0]
  exact hintc3_2_0_0

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT3_2_0_mem_gInterSpace :
    gtOfT ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 T3_2_0 ∈ gInterSpace ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 hT3_2_0 hAint3_2_0 hBint3_2_0 hCint3_2_0

theorem gtOfT3_2_0_ne_zero : gtOfT ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 T3_2_0 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) hsz3_2_0 T3_2_0_ne_zero

theorem gInterSpace3_2_0_ne_bot : gInterSpace ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT3_2_0_mem_gInterSpace, gtOfT3_2_0_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_3_2_0 : gParity ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (0 : ZMod 8) gInterSpace3_2_0_ne_bot).symm

end Triple_3_2_0

end G3_15
end TripleCerts
end GaugeChi
end Superfusion

/-! ### Kernel self-check -/

#print axioms Superfusion.GaugeChi.TripleCerts.G3_15.gParity_3_1_3
#print axioms Superfusion.GaugeChi.TripleCerts.G3_15.gParity_3_1_4
#print axioms Superfusion.GaugeChi.TripleCerts.G3_15.gParity_3_1_5
#print axioms Superfusion.GaugeChi.TripleCerts.G3_15.gParity_3_1_6
#print axioms Superfusion.GaugeChi.TripleCerts.G3_15.gParity_3_1_7
#print axioms Superfusion.GaugeChi.TripleCerts.G3_15.gParity_3_2_0
